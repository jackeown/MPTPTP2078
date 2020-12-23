%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:31 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 138 expanded)
%              Number of clauses        :   34 (  55 expanded)
%              Number of leaves         :    9 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  197 ( 687 expanded)
%              Number of equality atoms :   62 ( 153 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   2 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_9,negated_conjecture,(
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

fof(c_0_10,plain,(
    ! [X18,X19,X20] :
      ( ( r2_hidden(X18,k1_relat_1(X20))
        | ~ r2_hidden(k4_tarski(X18,X19),X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( X19 = k1_funct_1(X20,X18)
        | ~ r2_hidden(k4_tarski(X18,X19),X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( ~ r2_hidden(X18,k1_relat_1(X20))
        | X19 != k1_funct_1(X20,X18)
        | r2_hidden(k4_tarski(X18,X19),X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_11,plain,(
    ! [X13,X14,X15,X17] :
      ( ( r2_hidden(esk2_3(X13,X14,X15),k1_relat_1(X15))
        | ~ r2_hidden(X13,k9_relat_1(X15,X14))
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(esk2_3(X13,X14,X15),X13),X15)
        | ~ r2_hidden(X13,k9_relat_1(X15,X14))
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(esk2_3(X13,X14,X15),X14)
        | ~ r2_hidden(X13,k9_relat_1(X15,X14))
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(X17,k1_relat_1(X15))
        | ~ r2_hidden(k4_tarski(X17,X13),X15)
        | ~ r2_hidden(X17,X14)
        | r2_hidden(X13,k9_relat_1(X15,X14))
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_12,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | v1_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_13,negated_conjecture,(
    ! [X39] :
      ( v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,esk3_0,esk4_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
      & r2_hidden(esk7_0,k7_relset_1(esk3_0,esk4_0,esk6_0,esk5_0))
      & ( ~ r2_hidden(X39,esk3_0)
        | ~ r2_hidden(X39,esk5_0)
        | esk7_0 != k1_funct_1(esk6_0,X39) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_14,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | k1_relset_1(X24,X25,X26) = k1_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_15,plain,(
    ! [X31,X32,X33] :
      ( ( ~ v1_funct_2(X33,X31,X32)
        | X31 = k1_relset_1(X31,X32,X33)
        | X32 = k1_xboole_0
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( X31 != k1_relset_1(X31,X32,X33)
        | v1_funct_2(X33,X31,X32)
        | X32 = k1_xboole_0
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( ~ v1_funct_2(X33,X31,X32)
        | X31 = k1_relset_1(X31,X32,X33)
        | X31 != k1_xboole_0
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( X31 != k1_relset_1(X31,X32,X33)
        | v1_funct_2(X33,X31,X32)
        | X31 != k1_xboole_0
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( ~ v1_funct_2(X33,X31,X32)
        | X33 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 != k1_xboole_0
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( X33 != k1_xboole_0
        | v1_funct_2(X33,X31,X32)
        | X31 = k1_xboole_0
        | X32 != k1_xboole_0
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_16,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk5_0)
    | esk7_0 != k1_funct_1(esk6_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( k1_funct_1(X1,esk2_3(X2,X3,X1)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,plain,
    ( X1 = k1_relat_1(X2)
    | X1 != k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( esk7_0 != X1
    | ~ r2_hidden(esk2_3(X1,X2,esk6_0),esk3_0)
    | ~ r2_hidden(esk2_3(X1,X2,esk6_0),esk5_0)
    | ~ r2_hidden(X1,k9_relat_1(esk6_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_32,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_19])])).

cnf(c_0_34,negated_conjecture,
    ( esk3_0 = k1_relat_1(esk6_0)
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_28]),c_0_19])])).

cnf(c_0_35,negated_conjecture,
    ( esk3_0 = k1_relat_1(esk6_0)
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_28]),c_0_19])])).

fof(c_0_36,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_37,plain,(
    ! [X27,X28,X29,X30] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | k7_relset_1(X27,X28,X29,X30) = k9_relat_1(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_38,negated_conjecture,
    ( esk7_0 != X1
    | ~ r2_hidden(esk2_3(X1,esk5_0,esk6_0),esk3_0)
    | ~ r2_hidden(X1,k9_relat_1(esk6_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_26])])).

cnf(c_0_39,negated_conjecture,
    ( esk3_0 = k1_relat_1(esk6_0)
    | esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_40,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk7_0,k7_relset_1(esk3_0,esk4_0,esk6_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 != X1
    | ~ r2_hidden(esk2_3(X1,esk5_0,esk6_0),k1_relat_1(esk6_0))
    | ~ r2_hidden(X1,k9_relat_1(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk7_0,k9_relat_1(esk6_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_19])])).

cnf(c_0_47,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 != X1
    | ~ r2_hidden(X1,k9_relat_1(esk6_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_26])])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_26])])).

cnf(c_0_49,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_46])).

cnf(c_0_50,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:58:20 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.14/0.40  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.14/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.40  #
% 0.14/0.40  # Preprocessing time       : 0.028 s
% 0.14/0.40  # Presaturation interreduction done
% 0.14/0.40  
% 0.14/0.40  # Proof found!
% 0.14/0.40  # SZS status Theorem
% 0.14/0.40  # SZS output start CNFRefutation
% 0.14/0.40  fof(t115_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 0.14/0.40  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.14/0.40  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.14/0.40  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.14/0.40  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.14/0.40  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.14/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.14/0.40  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.14/0.40  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.14/0.40  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6))))))), inference(assume_negation,[status(cth)],[t115_funct_2])).
% 0.14/0.40  fof(c_0_10, plain, ![X18, X19, X20]:(((r2_hidden(X18,k1_relat_1(X20))|~r2_hidden(k4_tarski(X18,X19),X20)|(~v1_relat_1(X20)|~v1_funct_1(X20)))&(X19=k1_funct_1(X20,X18)|~r2_hidden(k4_tarski(X18,X19),X20)|(~v1_relat_1(X20)|~v1_funct_1(X20))))&(~r2_hidden(X18,k1_relat_1(X20))|X19!=k1_funct_1(X20,X18)|r2_hidden(k4_tarski(X18,X19),X20)|(~v1_relat_1(X20)|~v1_funct_1(X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.14/0.40  fof(c_0_11, plain, ![X13, X14, X15, X17]:((((r2_hidden(esk2_3(X13,X14,X15),k1_relat_1(X15))|~r2_hidden(X13,k9_relat_1(X15,X14))|~v1_relat_1(X15))&(r2_hidden(k4_tarski(esk2_3(X13,X14,X15),X13),X15)|~r2_hidden(X13,k9_relat_1(X15,X14))|~v1_relat_1(X15)))&(r2_hidden(esk2_3(X13,X14,X15),X14)|~r2_hidden(X13,k9_relat_1(X15,X14))|~v1_relat_1(X15)))&(~r2_hidden(X17,k1_relat_1(X15))|~r2_hidden(k4_tarski(X17,X13),X15)|~r2_hidden(X17,X14)|r2_hidden(X13,k9_relat_1(X15,X14))|~v1_relat_1(X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.14/0.40  fof(c_0_12, plain, ![X21, X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|v1_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.14/0.40  fof(c_0_13, negated_conjecture, ![X39]:(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk3_0,esk4_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&(r2_hidden(esk7_0,k7_relset_1(esk3_0,esk4_0,esk6_0,esk5_0))&(~r2_hidden(X39,esk3_0)|~r2_hidden(X39,esk5_0)|esk7_0!=k1_funct_1(esk6_0,X39)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.14/0.40  fof(c_0_14, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|k1_relset_1(X24,X25,X26)=k1_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.14/0.40  fof(c_0_15, plain, ![X31, X32, X33]:((((~v1_funct_2(X33,X31,X32)|X31=k1_relset_1(X31,X32,X33)|X32=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))&(X31!=k1_relset_1(X31,X32,X33)|v1_funct_2(X33,X31,X32)|X32=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))&((~v1_funct_2(X33,X31,X32)|X31=k1_relset_1(X31,X32,X33)|X31!=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))&(X31!=k1_relset_1(X31,X32,X33)|v1_funct_2(X33,X31,X32)|X31!=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))))&((~v1_funct_2(X33,X31,X32)|X33=k1_xboole_0|X31=k1_xboole_0|X32!=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))&(X33!=k1_xboole_0|v1_funct_2(X33,X31,X32)|X31=k1_xboole_0|X32!=k1_xboole_0|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.14/0.40  cnf(c_0_16, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.40  cnf(c_0_17, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.40  cnf(c_0_18, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.40  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.40  cnf(c_0_20, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  cnf(c_0_21, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.40  cnf(c_0_22, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.40  cnf(c_0_23, negated_conjecture, (~r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk5_0)|esk7_0!=k1_funct_1(esk6_0,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.40  cnf(c_0_24, plain, (k1_funct_1(X1,esk2_3(X2,X3,X1))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.40  cnf(c_0_25, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.40  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.40  cnf(c_0_27, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.40  cnf(c_0_28, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.40  cnf(c_0_29, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.40  cnf(c_0_30, plain, (X1=k1_relat_1(X2)|X1!=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_20, c_0_22])).
% 0.14/0.40  cnf(c_0_31, negated_conjecture, (esk7_0!=X1|~r2_hidden(esk2_3(X1,X2,esk6_0),esk3_0)|~r2_hidden(esk2_3(X1,X2,esk6_0),esk5_0)|~r2_hidden(X1,k9_relat_1(esk6_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])])).
% 0.14/0.40  cnf(c_0_32, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.40  cnf(c_0_33, negated_conjecture, (esk6_0=k1_xboole_0|esk3_0=k1_xboole_0|esk4_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_19])])).
% 0.14/0.40  cnf(c_0_34, negated_conjecture, (esk3_0=k1_relat_1(esk6_0)|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_28]), c_0_19])])).
% 0.14/0.40  cnf(c_0_35, negated_conjecture, (esk3_0=k1_relat_1(esk6_0)|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_28]), c_0_19])])).
% 0.14/0.40  fof(c_0_36, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.14/0.40  fof(c_0_37, plain, ![X27, X28, X29, X30]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|k7_relset_1(X27,X28,X29,X30)=k9_relat_1(X29,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.14/0.40  cnf(c_0_38, negated_conjecture, (esk7_0!=X1|~r2_hidden(esk2_3(X1,esk5_0,esk6_0),esk3_0)|~r2_hidden(X1,k9_relat_1(esk6_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_26])])).
% 0.14/0.40  cnf(c_0_39, negated_conjecture, (esk3_0=k1_relat_1(esk6_0)|esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.14/0.40  cnf(c_0_40, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.40  cnf(c_0_41, negated_conjecture, (r2_hidden(esk7_0,k7_relset_1(esk3_0,esk4_0,esk6_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.40  cnf(c_0_42, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.14/0.40  cnf(c_0_43, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0!=X1|~r2_hidden(esk2_3(X1,esk5_0,esk6_0),k1_relat_1(esk6_0))|~r2_hidden(X1,k9_relat_1(esk6_0,esk5_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.14/0.40  cnf(c_0_44, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.40  cnf(c_0_45, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_40, c_0_17])).
% 0.14/0.40  cnf(c_0_46, negated_conjecture, (r2_hidden(esk7_0,k9_relat_1(esk6_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_19])])).
% 0.14/0.40  cnf(c_0_47, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0!=X1|~r2_hidden(X1,k9_relat_1(esk6_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_26])])).
% 0.14/0.40  cnf(c_0_48, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_26])])).
% 0.14/0.40  cnf(c_0_49, negated_conjecture, (esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_46])).
% 0.14/0.40  cnf(c_0_50, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.14/0.40  cnf(c_0_51, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_50])]), ['proof']).
% 0.14/0.40  # SZS output end CNFRefutation
% 0.14/0.40  # Proof object total steps             : 52
% 0.14/0.40  # Proof object clause steps            : 34
% 0.14/0.40  # Proof object formula steps           : 18
% 0.14/0.40  # Proof object conjectures             : 21
% 0.14/0.40  # Proof object clause conjectures      : 18
% 0.14/0.40  # Proof object formula conjectures     : 3
% 0.14/0.40  # Proof object initial clauses used    : 17
% 0.14/0.40  # Proof object initial formulas used   : 9
% 0.14/0.40  # Proof object generating inferences   : 16
% 0.14/0.40  # Proof object simplifying inferences  : 21
% 0.14/0.40  # Training examples: 0 positive, 0 negative
% 0.14/0.40  # Parsed axioms                        : 10
% 0.14/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.40  # Initial clauses                      : 28
% 0.14/0.40  # Removed in clause preprocessing      : 0
% 0.14/0.40  # Initial clauses in saturation        : 28
% 0.14/0.40  # Processed clauses                    : 172
% 0.14/0.40  # ...of these trivial                  : 0
% 0.14/0.40  # ...subsumed                          : 37
% 0.14/0.40  # ...remaining for further processing  : 135
% 0.14/0.40  # Other redundant clauses eliminated   : 1
% 0.14/0.40  # Clauses deleted for lack of memory   : 0
% 0.14/0.40  # Backward-subsumed                    : 1
% 0.14/0.40  # Backward-rewritten                   : 34
% 0.14/0.40  # Generated clauses                    : 217
% 0.14/0.40  # ...of the previous two non-trivial   : 201
% 0.14/0.40  # Contextual simplify-reflections      : 4
% 0.14/0.40  # Paramodulations                      : 212
% 0.14/0.40  # Factorizations                       : 0
% 0.14/0.40  # Equation resolutions                 : 4
% 0.14/0.40  # Propositional unsat checks           : 0
% 0.14/0.40  #    Propositional check models        : 0
% 0.14/0.40  #    Propositional check unsatisfiable : 0
% 0.14/0.40  #    Propositional clauses             : 0
% 0.14/0.40  #    Propositional clauses after purity: 0
% 0.14/0.40  #    Propositional unsat core size     : 0
% 0.14/0.40  #    Propositional preprocessing time  : 0.000
% 0.14/0.40  #    Propositional encoding time       : 0.000
% 0.14/0.40  #    Propositional solver time         : 0.000
% 0.14/0.40  #    Success case prop preproc time    : 0.000
% 0.14/0.40  #    Success case prop encoding time   : 0.000
% 0.14/0.40  #    Success case prop solver time     : 0.000
% 0.14/0.40  # Current number of processed clauses  : 71
% 0.14/0.40  #    Positive orientable unit clauses  : 3
% 0.14/0.40  #    Positive unorientable unit clauses: 0
% 0.14/0.40  #    Negative unit clauses             : 2
% 0.14/0.40  #    Non-unit-clauses                  : 66
% 0.14/0.40  # Current number of unprocessed clauses: 70
% 0.14/0.40  # ...number of literals in the above   : 367
% 0.14/0.40  # Current number of archived formulas  : 0
% 0.14/0.40  # Current number of archived clauses   : 64
% 0.14/0.40  # Clause-clause subsumption calls (NU) : 1112
% 0.14/0.40  # Rec. Clause-clause subsumption calls : 418
% 0.14/0.40  # Non-unit clause-clause subsumptions  : 33
% 0.14/0.40  # Unit Clause-clause subsumption calls : 24
% 0.14/0.40  # Rewrite failures with RHS unbound    : 0
% 0.14/0.40  # BW rewrite match attempts            : 2
% 0.14/0.40  # BW rewrite match successes           : 2
% 0.14/0.40  # Condensation attempts                : 0
% 0.14/0.40  # Condensation successes               : 0
% 0.14/0.40  # Termbank termtop insertions          : 5829
% 0.14/0.40  
% 0.14/0.40  # -------------------------------------------------
% 0.14/0.40  # User time                : 0.037 s
% 0.14/0.40  # System time              : 0.005 s
% 0.14/0.40  # Total time               : 0.043 s
% 0.14/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
