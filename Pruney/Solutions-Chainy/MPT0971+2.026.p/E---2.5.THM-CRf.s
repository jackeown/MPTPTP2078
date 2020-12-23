%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:40 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 158 expanded)
%              Number of clauses        :   24 (  63 expanded)
%              Number of leaves         :    9 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :  123 ( 519 expanded)
%              Number of equality atoms :   21 (  75 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ~ ( r2_hidden(X3,k2_relset_1(X1,X2,X4))
            & ! [X5] :
                ~ ( r2_hidden(X5,X1)
                  & k1_funct_1(X4,X5) = X3 ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_funct_2])).

fof(c_0_10,plain,(
    ! [X22,X23,X24] :
      ( ( v4_relat_1(X24,X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( v5_relat_1(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_11,negated_conjecture,(
    ! [X32] :
      ( v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,esk2_0,esk3_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
      & r2_hidden(esk4_0,k2_relset_1(esk2_0,esk3_0,esk5_0))
      & ( ~ r2_hidden(X32,esk2_0)
        | k1_funct_1(esk5_0,X32) != esk4_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_relat_1(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_13,plain,(
    ! [X8,X9] : v1_relat_1(k2_zfmisc_1(X8,X9)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_14,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | k2_relset_1(X25,X26,X27) = k2_relat_1(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_15,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ v4_relat_1(X18,X17)
      | X18 = k7_relat_1(X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_16,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | k2_relat_1(k7_relat_1(X16,X15)) = k9_relat_1(X16,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_22,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v4_relat_1(esk5_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_17]),c_0_19])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk4_0,k2_relset_1(esk2_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( k2_relset_1(esk2_0,esk3_0,esk5_0) = k2_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_17])).

cnf(c_0_27,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( k7_relat_1(esk5_0,esk2_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

fof(c_0_29,plain,(
    ! [X10,X11,X12,X14] :
      ( ( r2_hidden(esk1_3(X10,X11,X12),k1_relat_1(X12))
        | ~ r2_hidden(X10,k9_relat_1(X12,X11))
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(esk1_3(X10,X11,X12),X10),X12)
        | ~ r2_hidden(X10,k9_relat_1(X12,X11))
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | ~ r2_hidden(X10,k9_relat_1(X12,X11))
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(X14,k1_relat_1(X12))
        | ~ r2_hidden(k4_tarski(X14,X10),X12)
        | ~ r2_hidden(X14,X11)
        | r2_hidden(X10,k9_relat_1(X12,X11))
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk4_0,k2_relat_1(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( k2_relat_1(esk5_0) = k9_relat_1(esk5_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_24])])).

fof(c_0_32,plain,(
    ! [X19,X20,X21] :
      ( ( r2_hidden(X19,k1_relat_1(X21))
        | ~ r2_hidden(k4_tarski(X19,X20),X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( X20 = k1_funct_1(X21,X19)
        | ~ r2_hidden(k4_tarski(X19,X20),X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( ~ r2_hidden(X19,k1_relat_1(X21))
        | X20 != k1_funct_1(X21,X19)
        | r2_hidden(k4_tarski(X19,X20),X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk4_0,k9_relat_1(esk5_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_3(esk4_0,esk2_0,esk5_0),esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_24])])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(X1,esk2_0)
    | k1_funct_1(esk5_0,X1) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_3(esk4_0,esk2_0,esk5_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_24])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,esk2_0,esk5_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_34]),c_0_24])])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:35:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S011N
% 0.14/0.36  # and selection function PSelectDiffNegLit.
% 0.14/0.36  #
% 0.14/0.36  # Preprocessing time       : 0.016 s
% 0.14/0.36  # Presaturation interreduction done
% 0.14/0.36  
% 0.14/0.36  # Proof found!
% 0.14/0.36  # SZS status Theorem
% 0.14/0.36  # SZS output start CNFRefutation
% 0.14/0.36  fof(t17_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~((r2_hidden(X3,k2_relset_1(X1,X2,X4))&![X5]:~((r2_hidden(X5,X1)&k1_funct_1(X4,X5)=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 0.14/0.36  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.14/0.36  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.14/0.36  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.14/0.36  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.14/0.36  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 0.14/0.36  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.14/0.36  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.14/0.36  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.14/0.36  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>~((r2_hidden(X3,k2_relset_1(X1,X2,X4))&![X5]:~((r2_hidden(X5,X1)&k1_funct_1(X4,X5)=X3)))))), inference(assume_negation,[status(cth)],[t17_funct_2])).
% 0.14/0.36  fof(c_0_10, plain, ![X22, X23, X24]:((v4_relat_1(X24,X22)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))&(v5_relat_1(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.14/0.36  fof(c_0_11, negated_conjecture, ![X32]:(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk2_0,esk3_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(r2_hidden(esk4_0,k2_relset_1(esk2_0,esk3_0,esk5_0))&(~r2_hidden(X32,esk2_0)|k1_funct_1(esk5_0,X32)!=esk4_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.14/0.36  fof(c_0_12, plain, ![X6, X7]:(~v1_relat_1(X6)|(~m1_subset_1(X7,k1_zfmisc_1(X6))|v1_relat_1(X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.14/0.36  fof(c_0_13, plain, ![X8, X9]:v1_relat_1(k2_zfmisc_1(X8,X9)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.14/0.36  fof(c_0_14, plain, ![X25, X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|k2_relset_1(X25,X26,X27)=k2_relat_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.14/0.36  fof(c_0_15, plain, ![X17, X18]:(~v1_relat_1(X18)|~v4_relat_1(X18,X17)|X18=k7_relat_1(X18,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.14/0.36  cnf(c_0_16, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.36  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.36  cnf(c_0_18, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.36  cnf(c_0_19, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.36  cnf(c_0_20, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.36  fof(c_0_21, plain, ![X15, X16]:(~v1_relat_1(X16)|k2_relat_1(k7_relat_1(X16,X15))=k9_relat_1(X16,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.14/0.36  cnf(c_0_22, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.36  cnf(c_0_23, negated_conjecture, (v4_relat_1(esk5_0,esk2_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.36  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_17]), c_0_19])])).
% 0.14/0.36  cnf(c_0_25, negated_conjecture, (r2_hidden(esk4_0,k2_relset_1(esk2_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.36  cnf(c_0_26, negated_conjecture, (k2_relset_1(esk2_0,esk3_0,esk5_0)=k2_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_20, c_0_17])).
% 0.14/0.36  cnf(c_0_27, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.36  cnf(c_0_28, negated_conjecture, (k7_relat_1(esk5_0,esk2_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.14/0.36  fof(c_0_29, plain, ![X10, X11, X12, X14]:((((r2_hidden(esk1_3(X10,X11,X12),k1_relat_1(X12))|~r2_hidden(X10,k9_relat_1(X12,X11))|~v1_relat_1(X12))&(r2_hidden(k4_tarski(esk1_3(X10,X11,X12),X10),X12)|~r2_hidden(X10,k9_relat_1(X12,X11))|~v1_relat_1(X12)))&(r2_hidden(esk1_3(X10,X11,X12),X11)|~r2_hidden(X10,k9_relat_1(X12,X11))|~v1_relat_1(X12)))&(~r2_hidden(X14,k1_relat_1(X12))|~r2_hidden(k4_tarski(X14,X10),X12)|~r2_hidden(X14,X11)|r2_hidden(X10,k9_relat_1(X12,X11))|~v1_relat_1(X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.14/0.36  cnf(c_0_30, negated_conjecture, (r2_hidden(esk4_0,k2_relat_1(esk5_0))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.14/0.36  cnf(c_0_31, negated_conjecture, (k2_relat_1(esk5_0)=k9_relat_1(esk5_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_24])])).
% 0.14/0.36  fof(c_0_32, plain, ![X19, X20, X21]:(((r2_hidden(X19,k1_relat_1(X21))|~r2_hidden(k4_tarski(X19,X20),X21)|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(X20=k1_funct_1(X21,X19)|~r2_hidden(k4_tarski(X19,X20),X21)|(~v1_relat_1(X21)|~v1_funct_1(X21))))&(~r2_hidden(X19,k1_relat_1(X21))|X20!=k1_funct_1(X21,X19)|r2_hidden(k4_tarski(X19,X20),X21)|(~v1_relat_1(X21)|~v1_funct_1(X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.14/0.36  cnf(c_0_33, plain, (r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.36  cnf(c_0_34, negated_conjecture, (r2_hidden(esk4_0,k9_relat_1(esk5_0,esk2_0))), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.14/0.36  cnf(c_0_35, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.36  cnf(c_0_36, negated_conjecture, (r2_hidden(k4_tarski(esk1_3(esk4_0,esk2_0,esk5_0),esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_24])])).
% 0.14/0.36  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.36  cnf(c_0_38, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.36  cnf(c_0_39, negated_conjecture, (~r2_hidden(X1,esk2_0)|k1_funct_1(esk5_0,X1)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.36  cnf(c_0_40, negated_conjecture, (k1_funct_1(esk5_0,esk1_3(esk4_0,esk2_0,esk5_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_24])])).
% 0.14/0.36  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_3(esk4_0,esk2_0,esk5_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_34]), c_0_24])])).
% 0.14/0.36  cnf(c_0_42, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])]), ['proof']).
% 0.14/0.36  # SZS output end CNFRefutation
% 0.14/0.36  # Proof object total steps             : 43
% 0.14/0.36  # Proof object clause steps            : 24
% 0.14/0.36  # Proof object formula steps           : 19
% 0.14/0.36  # Proof object conjectures             : 18
% 0.14/0.36  # Proof object clause conjectures      : 15
% 0.14/0.36  # Proof object formula conjectures     : 3
% 0.14/0.36  # Proof object initial clauses used    : 13
% 0.14/0.36  # Proof object initial formulas used   : 9
% 0.14/0.36  # Proof object generating inferences   : 9
% 0.14/0.36  # Proof object simplifying inferences  : 17
% 0.14/0.36  # Training examples: 0 positive, 0 negative
% 0.14/0.36  # Parsed axioms                        : 9
% 0.14/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.36  # Initial clauses                      : 19
% 0.14/0.36  # Removed in clause preprocessing      : 0
% 0.14/0.36  # Initial clauses in saturation        : 19
% 0.14/0.36  # Processed clauses                    : 54
% 0.14/0.36  # ...of these trivial                  : 0
% 0.14/0.36  # ...subsumed                          : 0
% 0.14/0.36  # ...remaining for further processing  : 54
% 0.14/0.36  # Other redundant clauses eliminated   : 1
% 0.14/0.36  # Clauses deleted for lack of memory   : 0
% 0.14/0.36  # Backward-subsumed                    : 0
% 0.14/0.36  # Backward-rewritten                   : 3
% 0.14/0.36  # Generated clauses                    : 21
% 0.14/0.36  # ...of the previous two non-trivial   : 19
% 0.14/0.36  # Contextual simplify-reflections      : 0
% 0.14/0.36  # Paramodulations                      : 20
% 0.14/0.36  # Factorizations                       : 0
% 0.14/0.36  # Equation resolutions                 : 1
% 0.14/0.36  # Propositional unsat checks           : 0
% 0.14/0.36  #    Propositional check models        : 0
% 0.14/0.36  #    Propositional check unsatisfiable : 0
% 0.14/0.36  #    Propositional clauses             : 0
% 0.14/0.36  #    Propositional clauses after purity: 0
% 0.14/0.36  #    Propositional unsat core size     : 0
% 0.14/0.36  #    Propositional preprocessing time  : 0.000
% 0.14/0.36  #    Propositional encoding time       : 0.000
% 0.14/0.36  #    Propositional solver time         : 0.000
% 0.14/0.36  #    Success case prop preproc time    : 0.000
% 0.14/0.36  #    Success case prop encoding time   : 0.000
% 0.14/0.36  #    Success case prop solver time     : 0.000
% 0.14/0.36  # Current number of processed clauses  : 31
% 0.14/0.36  #    Positive orientable unit clauses  : 17
% 0.14/0.36  #    Positive unorientable unit clauses: 0
% 0.14/0.36  #    Negative unit clauses             : 0
% 0.14/0.36  #    Non-unit-clauses                  : 14
% 0.14/0.36  # Current number of unprocessed clauses: 2
% 0.14/0.36  # ...number of literals in the above   : 3
% 0.14/0.36  # Current number of archived formulas  : 0
% 0.14/0.36  # Current number of archived clauses   : 22
% 0.14/0.36  # Clause-clause subsumption calls (NU) : 76
% 0.14/0.36  # Rec. Clause-clause subsumption calls : 36
% 0.14/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.36  # Unit Clause-clause subsumption calls : 0
% 0.14/0.36  # Rewrite failures with RHS unbound    : 0
% 0.14/0.36  # BW rewrite match attempts            : 2
% 0.14/0.36  # BW rewrite match successes           : 2
% 0.14/0.36  # Condensation attempts                : 0
% 0.14/0.36  # Condensation successes               : 0
% 0.14/0.36  # Termbank termtop insertions          : 1897
% 0.14/0.36  
% 0.14/0.36  # -------------------------------------------------
% 0.14/0.36  # User time                : 0.019 s
% 0.14/0.36  # System time              : 0.001 s
% 0.14/0.36  # Total time               : 0.021 s
% 0.14/0.36  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
