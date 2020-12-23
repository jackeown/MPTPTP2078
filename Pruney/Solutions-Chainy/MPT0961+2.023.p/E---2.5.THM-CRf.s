%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:54 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 (1291 expanded)
%              Number of clauses        :   54 ( 588 expanded)
%              Number of leaves         :    9 ( 320 expanded)
%              Depth                    :   21
%              Number of atoms          :  195 (3947 expanded)
%              Number of equality atoms :   64 ( 871 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v1_funct_1(X1)
          & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    inference(assume_negation,[status(cth)],[t3_funct_2])).

fof(c_0_10,plain,(
    ! [X9] :
      ( ~ v1_relat_1(X9)
      | r1_tarski(X9,k2_zfmisc_1(k1_relat_1(X9),k2_relat_1(X9))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & ( ~ v1_funct_1(esk1_0)
      | ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
      | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X7,X8] :
      ( ( ~ m1_subset_1(X7,k1_zfmisc_1(X8))
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | m1_subset_1(X7,k1_zfmisc_1(X8)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( ~ v1_funct_1(esk1_0)
    | ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_19,plain,(
    ! [X19,X20,X21] :
      ( ( ~ v1_funct_2(X21,X19,X20)
        | X19 = k1_relset_1(X19,X20,X21)
        | X20 = k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X19 != k1_relset_1(X19,X20,X21)
        | v1_funct_2(X21,X19,X20)
        | X20 = k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( ~ v1_funct_2(X21,X19,X20)
        | X19 = k1_relset_1(X19,X20,X21)
        | X19 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X19 != k1_relset_1(X19,X20,X21)
        | v1_funct_2(X21,X19,X20)
        | X19 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( ~ v1_funct_2(X21,X19,X20)
        | X21 = k1_xboole_0
        | X19 = k1_xboole_0
        | X20 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X21 != k1_xboole_0
        | v1_funct_2(X21,X19,X20)
        | X19 = k1_xboole_0
        | X20 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_20,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16])])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_22,plain,(
    ! [X5,X6] :
      ( ( k2_zfmisc_1(X5,X6) != k1_xboole_0
        | X5 = k1_xboole_0
        | X6 = k1_xboole_0 )
      & ( X5 != k1_xboole_0
        | k2_zfmisc_1(X5,X6) = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X5,X6) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_23,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | X4 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_24,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])])).

fof(c_0_26,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | k1_relset_1(X16,X17,X18) = k1_relat_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_27,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k2_relat_1(esk1_0) = k1_xboole_0
    | k1_relset_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0),esk1_0) != k1_relat_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_21]),c_0_25])).

cnf(c_0_30,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk1_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( k2_relat_1(esk1_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_21])])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_39,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk1_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k1_xboole_0)
    | ~ v1_xboole_0(k2_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_28])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | k2_zfmisc_1(X1,X1) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_2(esk1_0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,esk1_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_35]),c_0_37])])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(k2_zfmisc_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_28])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_2(esk1_0,k1_xboole_0,X1)
    | k1_relat_1(esk1_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_30]),c_0_33]),c_0_40])])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),X1)
    | ~ v1_xboole_0(k2_zfmisc_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(esk1_0,k1_xboole_0,X1)
    | ~ v1_xboole_0(k1_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_28])).

fof(c_0_49,plain,(
    ! [X10,X11,X12] :
      ( ~ v1_xboole_0(X10)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | v1_xboole_0(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(X1,X1))
    | ~ v1_xboole_0(k1_relat_1(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_28]),c_0_48])).

cnf(c_0_51,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_28])).

cnf(c_0_52,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(X1,X1))
    | ~ v1_xboole_0(k1_relat_1(X2))
    | ~ v1_xboole_0(esk1_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_33]),c_0_37])])).

cnf(c_0_55,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 = k1_xboole_0
    | X1 != k1_xboole_0
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_28])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(X1,X1))
    | ~ v1_xboole_0(k1_relat_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_40])])).

cnf(c_0_58,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_28])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_55])]),c_0_36])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_54]),c_0_40])])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_33]),c_0_37])])).

cnf(c_0_62,negated_conjecture,
    ( ~ v1_funct_2(X1,k1_relat_1(X1),X1)
    | ~ v1_xboole_0(esk1_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_28])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])])).

cnf(c_0_64,negated_conjecture,
    ( ~ m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_funct_2(X1,k1_relat_1(X1),X1)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_54]),c_0_40])])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( ~ m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_51]),c_0_37])])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k1_relat_1(k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_37])])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_37])])).

cnf(c_0_70,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_63]),c_0_37])])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_70]),c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.48  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 0.20/0.48  # and selection function PSelectUnlessUniqMaxPos.
% 0.20/0.48  #
% 0.20/0.48  # Preprocessing time       : 0.028 s
% 0.20/0.48  # Presaturation interreduction done
% 0.20/0.48  
% 0.20/0.48  # Proof found!
% 0.20/0.48  # SZS status Theorem
% 0.20/0.48  # SZS output start CNFRefutation
% 0.20/0.48  fof(t3_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.20/0.48  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 0.20/0.48  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.48  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.48  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.48  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.48  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.48  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.48  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 0.20/0.48  fof(c_0_9, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))))), inference(assume_negation,[status(cth)],[t3_funct_2])).
% 0.20/0.48  fof(c_0_10, plain, ![X9]:(~v1_relat_1(X9)|r1_tarski(X9,k2_zfmisc_1(k1_relat_1(X9),k2_relat_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.20/0.48  fof(c_0_11, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&(~v1_funct_1(esk1_0)|~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.20/0.48  fof(c_0_12, plain, ![X7, X8]:((~m1_subset_1(X7,k1_zfmisc_1(X8))|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|m1_subset_1(X7,k1_zfmisc_1(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.48  cnf(c_0_13, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.48  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.48  cnf(c_0_15, negated_conjecture, (~v1_funct_1(esk1_0)|~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.48  cnf(c_0_16, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.48  cnf(c_0_17, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.48  cnf(c_0_18, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.48  fof(c_0_19, plain, ![X19, X20, X21]:((((~v1_funct_2(X21,X19,X20)|X19=k1_relset_1(X19,X20,X21)|X20=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))&(X19!=k1_relset_1(X19,X20,X21)|v1_funct_2(X21,X19,X20)|X20=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))&((~v1_funct_2(X21,X19,X20)|X19=k1_relset_1(X19,X20,X21)|X19!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))&(X19!=k1_relset_1(X19,X20,X21)|v1_funct_2(X21,X19,X20)|X19!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))))&((~v1_funct_2(X21,X19,X20)|X21=k1_xboole_0|X19=k1_xboole_0|X20!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))&(X21!=k1_xboole_0|v1_funct_2(X21,X19,X20)|X19=k1_xboole_0|X20!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.48  cnf(c_0_20, negated_conjecture, (~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16])])).
% 0.20/0.48  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.48  fof(c_0_22, plain, ![X5, X6]:((k2_zfmisc_1(X5,X6)!=k1_xboole_0|(X5=k1_xboole_0|X6=k1_xboole_0))&((X5!=k1_xboole_0|k2_zfmisc_1(X5,X6)=k1_xboole_0)&(X6!=k1_xboole_0|k2_zfmisc_1(X5,X6)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.48  fof(c_0_23, plain, ![X4]:(~v1_xboole_0(X4)|X4=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.48  cnf(c_0_24, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.48  cnf(c_0_25, negated_conjecture, (~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21])])).
% 0.20/0.48  fof(c_0_26, plain, ![X16, X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|k1_relset_1(X16,X17,X18)=k1_relat_1(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.48  cnf(c_0_27, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.48  cnf(c_0_28, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.48  cnf(c_0_29, negated_conjecture, (k2_relat_1(esk1_0)=k1_xboole_0|k1_relset_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0),esk1_0)!=k1_relat_1(esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_21]), c_0_25])).
% 0.20/0.48  cnf(c_0_30, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.48  cnf(c_0_31, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.48  cnf(c_0_32, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.48  cnf(c_0_33, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_27])).
% 0.20/0.48  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk1_0,k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))), inference(spm,[status(thm)],[c_0_21, c_0_28])).
% 0.20/0.48  cnf(c_0_35, negated_conjecture, (k2_relat_1(esk1_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_21])])).
% 0.20/0.48  cnf(c_0_36, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_31])).
% 0.20/0.48  cnf(c_0_37, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.48  cnf(c_0_38, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.48  cnf(c_0_39, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_32]), c_0_33])).
% 0.20/0.48  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk1_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37])])).
% 0.20/0.48  cnf(c_0_41, negated_conjecture, (~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k1_xboole_0)|~v1_xboole_0(k2_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_25, c_0_28])).
% 0.20/0.48  cnf(c_0_42, plain, (X1=k1_xboole_0|k2_zfmisc_1(X1,X1)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_38])).
% 0.20/0.48  cnf(c_0_43, negated_conjecture, (v1_funct_2(esk1_0,k1_xboole_0,X1)|k1_relset_1(k1_xboole_0,X1,esk1_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.48  cnf(c_0_44, negated_conjecture, (~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_35]), c_0_37])])).
% 0.20/0.48  cnf(c_0_45, plain, (X1=k1_xboole_0|~v1_xboole_0(k2_zfmisc_1(X1,X1))), inference(spm,[status(thm)],[c_0_42, c_0_28])).
% 0.20/0.48  cnf(c_0_46, negated_conjecture, (v1_funct_2(esk1_0,k1_xboole_0,X1)|k1_relat_1(esk1_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_30]), c_0_33]), c_0_40])])).
% 0.20/0.48  cnf(c_0_47, negated_conjecture, (~v1_funct_2(esk1_0,k1_relat_1(esk1_0),X1)|~v1_xboole_0(k2_zfmisc_1(X1,X1))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.48  cnf(c_0_48, negated_conjecture, (v1_funct_2(esk1_0,k1_xboole_0,X1)|~v1_xboole_0(k1_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_46, c_0_28])).
% 0.20/0.48  fof(c_0_49, plain, ![X10, X11, X12]:(~v1_xboole_0(X10)|(~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|v1_xboole_0(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 0.20/0.48  cnf(c_0_50, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(X1,X1))|~v1_xboole_0(k1_relat_1(esk1_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_28]), c_0_48])).
% 0.20/0.48  cnf(c_0_51, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_28, c_0_28])).
% 0.20/0.48  cnf(c_0_52, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.48  cnf(c_0_53, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(X1,X1))|~v1_xboole_0(k1_relat_1(X2))|~v1_xboole_0(esk1_0)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.48  cnf(c_0_54, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_33]), c_0_37])])).
% 0.20/0.48  cnf(c_0_55, plain, (v1_funct_2(X1,X2,X3)|X2=k1_xboole_0|X1!=k1_xboole_0|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.48  cnf(c_0_56, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(esk1_0)), inference(spm,[status(thm)],[c_0_40, c_0_28])).
% 0.20/0.48  cnf(c_0_57, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(X1,X1))|~v1_xboole_0(k1_relat_1(X2))|~v1_xboole_0(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_40])])).
% 0.20/0.48  cnf(c_0_58, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)|~v1_xboole_0(esk1_0)), inference(spm,[status(thm)],[c_0_44, c_0_28])).
% 0.20/0.48  cnf(c_0_59, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,X1,k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_55])]), c_0_36])).
% 0.20/0.48  cnf(c_0_60, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_54]), c_0_40])])).
% 0.20/0.48  cnf(c_0_61, negated_conjecture, (~v1_xboole_0(k1_relat_1(X1))|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_33]), c_0_37])])).
% 0.20/0.48  cnf(c_0_62, negated_conjecture, (~v1_funct_2(X1,k1_relat_1(X1),X1)|~v1_xboole_0(esk1_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_58, c_0_28])).
% 0.20/0.48  cnf(c_0_63, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60])])).
% 0.20/0.48  cnf(c_0_64, negated_conjecture, (~m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_61, c_0_54])).
% 0.20/0.48  cnf(c_0_65, negated_conjecture, (~v1_funct_2(X1,k1_relat_1(X1),X1)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_54]), c_0_40])])).
% 0.20/0.48  cnf(c_0_66, negated_conjecture, (v1_funct_2(k1_xboole_0,X1,k1_xboole_0)|m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_60, c_0_63])).
% 0.20/0.48  cnf(c_0_67, negated_conjecture, (~m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_51]), c_0_37])])).
% 0.20/0.48  cnf(c_0_68, negated_conjecture, (m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k1_relat_1(k1_xboole_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_37])])).
% 0.20/0.48  cnf(c_0_69, negated_conjecture, (~v1_xboole_0(k1_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_37])])).
% 0.20/0.48  cnf(c_0_70, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_63]), c_0_37])])).
% 0.20/0.48  cnf(c_0_71, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_70]), c_0_37])]), ['proof']).
% 0.20/0.48  # SZS output end CNFRefutation
% 0.20/0.48  # Proof object total steps             : 72
% 0.20/0.48  # Proof object clause steps            : 54
% 0.20/0.48  # Proof object formula steps           : 18
% 0.20/0.48  # Proof object conjectures             : 36
% 0.20/0.48  # Proof object clause conjectures      : 33
% 0.20/0.48  # Proof object formula conjectures     : 3
% 0.20/0.48  # Proof object initial clauses used    : 15
% 0.20/0.48  # Proof object initial formulas used   : 9
% 0.20/0.48  # Proof object generating inferences   : 30
% 0.20/0.48  # Proof object simplifying inferences  : 47
% 0.20/0.48  # Training examples: 0 positive, 0 negative
% 0.20/0.48  # Parsed axioms                        : 10
% 0.20/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.48  # Initial clauses                      : 20
% 0.20/0.48  # Removed in clause preprocessing      : 0
% 0.20/0.48  # Initial clauses in saturation        : 20
% 0.20/0.48  # Processed clauses                    : 1063
% 0.20/0.48  # ...of these trivial                  : 24
% 0.20/0.48  # ...subsumed                          : 741
% 0.20/0.48  # ...remaining for further processing  : 298
% 0.20/0.48  # Other redundant clauses eliminated   : 96
% 0.20/0.48  # Clauses deleted for lack of memory   : 0
% 0.20/0.48  # Backward-subsumed                    : 36
% 0.20/0.48  # Backward-rewritten                   : 25
% 0.20/0.48  # Generated clauses                    : 7910
% 0.20/0.48  # ...of the previous two non-trivial   : 7405
% 0.20/0.48  # Contextual simplify-reflections      : 1
% 0.20/0.48  # Paramodulations                      : 7763
% 0.20/0.48  # Factorizations                       : 52
% 0.20/0.48  # Equation resolutions                 : 96
% 0.20/0.48  # Propositional unsat checks           : 0
% 0.20/0.48  #    Propositional check models        : 0
% 0.20/0.48  #    Propositional check unsatisfiable : 0
% 0.20/0.48  #    Propositional clauses             : 0
% 0.20/0.48  #    Propositional clauses after purity: 0
% 0.20/0.48  #    Propositional unsat core size     : 0
% 0.20/0.48  #    Propositional preprocessing time  : 0.000
% 0.20/0.48  #    Propositional encoding time       : 0.000
% 0.20/0.48  #    Propositional solver time         : 0.000
% 0.20/0.48  #    Success case prop preproc time    : 0.000
% 0.20/0.48  #    Success case prop encoding time   : 0.000
% 0.20/0.48  #    Success case prop solver time     : 0.000
% 0.20/0.48  # Current number of processed clauses  : 211
% 0.20/0.48  #    Positive orientable unit clauses  : 14
% 0.20/0.48  #    Positive unorientable unit clauses: 0
% 0.20/0.48  #    Negative unit clauses             : 5
% 0.20/0.48  #    Non-unit-clauses                  : 192
% 0.20/0.48  # Current number of unprocessed clauses: 6171
% 0.20/0.48  # ...number of literals in the above   : 24214
% 0.20/0.48  # Current number of archived formulas  : 0
% 0.20/0.48  # Current number of archived clauses   : 81
% 0.20/0.48  # Clause-clause subsumption calls (NU) : 6308
% 0.20/0.48  # Rec. Clause-clause subsumption calls : 4577
% 0.20/0.48  # Non-unit clause-clause subsumptions  : 748
% 0.20/0.48  # Unit Clause-clause subsumption calls : 103
% 0.20/0.48  # Rewrite failures with RHS unbound    : 0
% 0.20/0.48  # BW rewrite match attempts            : 10
% 0.20/0.48  # BW rewrite match successes           : 8
% 0.20/0.48  # Condensation attempts                : 0
% 0.20/0.48  # Condensation successes               : 0
% 0.20/0.48  # Termbank termtop insertions          : 83861
% 0.20/0.48  
% 0.20/0.48  # -------------------------------------------------
% 0.20/0.48  # User time                : 0.121 s
% 0.20/0.48  # System time              : 0.010 s
% 0.20/0.48  # Total time               : 0.131 s
% 0.20/0.48  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
