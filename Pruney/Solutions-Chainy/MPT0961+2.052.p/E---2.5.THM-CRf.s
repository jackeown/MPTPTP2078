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
% DateTime   : Thu Dec  3 11:00:58 EST 2020

% Result     : Theorem 11.36s
% Output     : CNFRefutation 11.36s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 613 expanded)
%              Number of clauses        :   43 ( 299 expanded)
%              Number of leaves         :    9 ( 144 expanded)
%              Depth                    :   12
%              Number of atoms          :  196 (2240 expanded)
%              Number of equality atoms :   80 ( 719 expanded)
%              Maximal formula depth    :   14 (   4 average)
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

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

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

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v1_funct_1(X1)
          & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    inference(assume_negation,[status(cth)],[t3_funct_2])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & ( ~ v1_funct_1(esk1_0)
      | ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
      | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_11,plain,(
    ! [X12] :
      ( ( k1_relat_1(X12) != k1_xboole_0
        | X12 = k1_xboole_0
        | ~ v1_relat_1(X12) )
      & ( k2_relat_1(X12) != k1_xboole_0
        | X12 = k1_xboole_0
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_12,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_13,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_14,negated_conjecture,
    ( ~ v1_funct_1(esk1_0)
    | ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_20,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15])])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17])])).

cnf(c_0_22,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_23,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_24,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_27,plain,(
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

cnf(c_0_28,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_29,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ r1_tarski(k1_relat_1(X18),X16)
      | ~ r1_tarski(k2_relat_1(X18),X17)
      | m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(esk1_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_funct_2(X1,X1,X1)
    | ~ r1_tarski(k2_relat_1(esk1_0),X1)
    | ~ r1_tarski(X1,k2_relat_1(esk1_0))
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_17])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_33])).

cnf(c_0_39,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_24])).

fof(c_0_40,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | k1_relset_1(X13,X14,X15) = k1_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_funct_2(k2_relat_1(esk1_0),k2_relat_1(esk1_0),k2_relat_1(esk1_0))
    | ~ r1_tarski(k2_relat_1(esk1_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_36]),c_0_36])])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | ~ v1_funct_2(X1,X1,k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(ef,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_25])).

cnf(c_0_45,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_funct_2(k2_relat_1(esk1_0),k2_relat_1(esk1_0),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k2_relat_1(esk1_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_36])])).

cnf(c_0_49,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_22]),c_0_24]),c_0_25])])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | k2_zfmisc_1(X1,X1) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_26])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_funct_2(k2_relat_1(esk1_0),k2_relat_1(esk1_0),k1_xboole_0)
    | ~ m1_subset_1(k2_relat_1(esk1_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49])])).

cnf(c_0_53,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X1,X1))
    | ~ r1_tarski(k2_zfmisc_1(X1,X1),k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_17])])).

cnf(c_0_54,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_51])])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k2_relat_1(esk1_0),k2_relat_1(esk1_0)))
    | ~ r1_tarski(k2_zfmisc_1(k2_relat_1(esk1_0),k2_relat_1(esk1_0)),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_49]),c_0_25])])).

cnf(c_0_57,negated_conjecture,
    ( k2_relat_1(esk1_0) = k1_xboole_0
    | k1_relset_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0),esk1_0) != k1_relat_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_51]),c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( ~ v1_funct_2(k2_zfmisc_1(k2_relat_1(esk1_0),k2_relat_1(esk1_0)),k2_zfmisc_1(k2_relat_1(esk1_0),k2_relat_1(esk1_0)),k1_xboole_0)
    | ~ m1_subset_1(k2_zfmisc_1(k2_relat_1(esk1_0),k2_relat_1(esk1_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_43]),c_0_36])])).

cnf(c_0_59,negated_conjecture,
    ( k2_relat_1(esk1_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_45]),c_0_51])])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_59]),c_0_24]),c_0_59]),c_0_59]),c_0_24]),c_0_49]),c_0_59]),c_0_59]),c_0_24]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.31  % Computer   : n003.cluster.edu
% 0.13/0.31  % Model      : x86_64 x86_64
% 0.13/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.31  % Memory     : 8042.1875MB
% 0.13/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 10:23:27 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  # Version: 2.5pre002
% 0.13/0.32  # No SInE strategy applied
% 0.13/0.32  # Trying AutoSched0 for 299 seconds
% 11.36/11.57  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 11.36/11.57  # and selection function PSelectUnlessUniqMaxPos.
% 11.36/11.57  #
% 11.36/11.57  # Preprocessing time       : 0.042 s
% 11.36/11.57  # Presaturation interreduction done
% 11.36/11.57  
% 11.36/11.57  # Proof found!
% 11.36/11.57  # SZS status Theorem
% 11.36/11.57  # SZS output start CNFRefutation
% 11.36/11.57  fof(t3_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 11.36/11.57  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 11.36/11.57  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.36/11.57  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.36/11.57  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 11.36/11.57  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 11.36/11.57  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 11.36/11.57  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 11.36/11.57  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.36/11.57  fof(c_0_9, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))))), inference(assume_negation,[status(cth)],[t3_funct_2])).
% 11.36/11.57  fof(c_0_10, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&(~v1_funct_1(esk1_0)|~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 11.36/11.57  fof(c_0_11, plain, ![X12]:((k1_relat_1(X12)!=k1_xboole_0|X12=k1_xboole_0|~v1_relat_1(X12))&(k2_relat_1(X12)!=k1_xboole_0|X12=k1_xboole_0|~v1_relat_1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 11.36/11.57  fof(c_0_12, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 11.36/11.57  fof(c_0_13, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 11.36/11.57  cnf(c_0_14, negated_conjecture, (~v1_funct_1(esk1_0)|~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 11.36/11.57  cnf(c_0_15, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 11.36/11.57  cnf(c_0_16, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 11.36/11.57  cnf(c_0_17, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 11.36/11.57  cnf(c_0_18, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 11.36/11.57  fof(c_0_19, plain, ![X8]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 11.36/11.57  cnf(c_0_20, negated_conjecture, (~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15])])).
% 11.36/11.57  cnf(c_0_21, plain, (X1=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),k1_xboole_0)|~r1_tarski(k1_xboole_0,k2_relat_1(X1))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17])])).
% 11.36/11.57  cnf(c_0_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 11.36/11.57  cnf(c_0_23, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 11.36/11.57  cnf(c_0_24, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_18])).
% 11.36/11.57  cnf(c_0_25, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 11.36/11.57  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 11.36/11.57  fof(c_0_27, plain, ![X19, X20, X21]:((((~v1_funct_2(X21,X19,X20)|X19=k1_relset_1(X19,X20,X21)|X20=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))&(X19!=k1_relset_1(X19,X20,X21)|v1_funct_2(X21,X19,X20)|X20=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))&((~v1_funct_2(X21,X19,X20)|X19=k1_relset_1(X19,X20,X21)|X19!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))&(X19!=k1_relset_1(X19,X20,X21)|v1_funct_2(X21,X19,X20)|X19!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))))&((~v1_funct_2(X21,X19,X20)|X21=k1_xboole_0|X19=k1_xboole_0|X20!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))&(X21!=k1_xboole_0|v1_funct_2(X21,X19,X20)|X19=k1_xboole_0|X20!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 11.36/11.57  cnf(c_0_28, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 11.36/11.57  fof(c_0_29, plain, ![X16, X17, X18]:(~v1_relat_1(X18)|(~r1_tarski(k1_relat_1(X18),X16)|~r1_tarski(k2_relat_1(X18),X17)|m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 11.36/11.57  cnf(c_0_30, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 11.36/11.57  cnf(c_0_31, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)|~r1_tarski(k2_relat_1(esk1_0),k1_xboole_0)|~r1_tarski(k1_xboole_0,k2_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])])).
% 11.36/11.57  cnf(c_0_32, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 11.36/11.57  cnf(c_0_33, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_28])).
% 11.36/11.57  cnf(c_0_34, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 11.36/11.57  cnf(c_0_35, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 11.36/11.57  cnf(c_0_36, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_30])).
% 11.36/11.57  cnf(c_0_37, negated_conjecture, (~v1_funct_2(X1,X1,X1)|~r1_tarski(k2_relat_1(esk1_0),X1)|~r1_tarski(X1,k2_relat_1(esk1_0))|~r1_tarski(X1,k1_xboole_0)|~r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_31, c_0_17])).
% 11.36/11.57  cnf(c_0_38, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_32]), c_0_33])).
% 11.36/11.57  cnf(c_0_39, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_34]), c_0_24])).
% 11.36/11.57  fof(c_0_40, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|k1_relset_1(X13,X14,X15)=k1_relat_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 11.36/11.57  cnf(c_0_41, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 11.36/11.57  cnf(c_0_42, negated_conjecture, (~v1_funct_2(k2_relat_1(esk1_0),k2_relat_1(esk1_0),k2_relat_1(esk1_0))|~r1_tarski(k2_relat_1(esk1_0),k1_xboole_0)|~r1_tarski(k1_xboole_0,k2_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_36]), c_0_36])])).
% 11.36/11.57  cnf(c_0_43, plain, (X1=k1_xboole_0|~v1_funct_2(X1,X1,k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(ef,[status(thm)],[c_0_38])).
% 11.36/11.57  cnf(c_0_44, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|k1_relset_1(k1_xboole_0,X1,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_25])).
% 11.36/11.57  cnf(c_0_45, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 11.36/11.57  cnf(c_0_46, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 11.36/11.57  cnf(c_0_47, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_36])).
% 11.36/11.57  cnf(c_0_48, negated_conjecture, (~v1_funct_2(k2_relat_1(esk1_0),k2_relat_1(esk1_0),k1_xboole_0)|~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)|~m1_subset_1(k2_relat_1(esk1_0),k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_36])])).
% 11.36/11.57  cnf(c_0_49, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_22]), c_0_24]), c_0_25])])).
% 11.36/11.57  cnf(c_0_50, plain, (X1=k1_xboole_0|k2_zfmisc_1(X1,X1)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_46])).
% 11.36/11.57  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))), inference(spm,[status(thm)],[c_0_47, c_0_26])).
% 11.36/11.57  cnf(c_0_52, negated_conjecture, (~v1_funct_2(k2_relat_1(esk1_0),k2_relat_1(esk1_0),k1_xboole_0)|~m1_subset_1(k2_relat_1(esk1_0),k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49])])).
% 11.36/11.57  cnf(c_0_53, plain, (X1=k1_xboole_0|~r1_tarski(k1_xboole_0,k2_zfmisc_1(X1,X1))|~r1_tarski(k2_zfmisc_1(X1,X1),k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_17])])).
% 11.36/11.57  cnf(c_0_54, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 11.36/11.57  cnf(c_0_55, negated_conjecture, (~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_51])])).
% 11.36/11.57  cnf(c_0_56, negated_conjecture, (~r1_tarski(k1_xboole_0,k2_zfmisc_1(k2_relat_1(esk1_0),k2_relat_1(esk1_0)))|~r1_tarski(k2_zfmisc_1(k2_relat_1(esk1_0),k2_relat_1(esk1_0)),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_49]), c_0_25])])).
% 11.36/11.57  cnf(c_0_57, negated_conjecture, (k2_relat_1(esk1_0)=k1_xboole_0|k1_relset_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0),esk1_0)!=k1_relat_1(esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_51]), c_0_55])).
% 11.36/11.57  cnf(c_0_58, negated_conjecture, (~v1_funct_2(k2_zfmisc_1(k2_relat_1(esk1_0),k2_relat_1(esk1_0)),k2_zfmisc_1(k2_relat_1(esk1_0),k2_relat_1(esk1_0)),k1_xboole_0)|~m1_subset_1(k2_zfmisc_1(k2_relat_1(esk1_0),k2_relat_1(esk1_0)),k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_43]), c_0_36])])).
% 11.36/11.57  cnf(c_0_59, negated_conjecture, (k2_relat_1(esk1_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_45]), c_0_51])])).
% 11.36/11.57  cnf(c_0_60, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_59]), c_0_24]), c_0_59]), c_0_59]), c_0_24]), c_0_49]), c_0_59]), c_0_59]), c_0_24]), c_0_25])]), ['proof']).
% 11.36/11.57  # SZS output end CNFRefutation
% 11.36/11.57  # Proof object total steps             : 61
% 11.36/11.57  # Proof object clause steps            : 43
% 11.36/11.57  # Proof object formula steps           : 18
% 11.36/11.57  # Proof object conjectures             : 19
% 11.36/11.57  # Proof object clause conjectures      : 16
% 11.36/11.57  # Proof object formula conjectures     : 3
% 11.36/11.57  # Proof object initial clauses used    : 17
% 11.36/11.57  # Proof object initial formulas used   : 9
% 11.36/11.57  # Proof object generating inferences   : 17
% 11.36/11.57  # Proof object simplifying inferences  : 51
% 11.36/11.57  # Training examples: 0 positive, 0 negative
% 11.36/11.57  # Parsed axioms                        : 10
% 11.36/11.57  # Removed by relevancy pruning/SinE    : 0
% 11.36/11.57  # Initial clauses                      : 23
% 11.36/11.57  # Removed in clause preprocessing      : 0
% 11.36/11.57  # Initial clauses in saturation        : 23
% 11.36/11.57  # Processed clauses                    : 21292
% 11.36/11.57  # ...of these trivial                  : 760
% 11.36/11.57  # ...subsumed                          : 18095
% 11.36/11.57  # ...remaining for further processing  : 2437
% 11.36/11.57  # Other redundant clauses eliminated   : 6024
% 11.36/11.57  # Clauses deleted for lack of memory   : 0
% 11.36/11.57  # Backward-subsumed                    : 224
% 11.36/11.57  # Backward-rewritten                   : 829
% 11.36/11.57  # Generated clauses                    : 2066973
% 11.36/11.57  # ...of the previous two non-trivial   : 1203115
% 11.36/11.57  # Contextual simplify-reflections      : 16
% 11.36/11.57  # Paramodulations                      : 2059988
% 11.36/11.57  # Factorizations                       : 962
% 11.36/11.57  # Equation resolutions                 : 6024
% 11.36/11.57  # Propositional unsat checks           : 0
% 11.36/11.57  #    Propositional check models        : 0
% 11.36/11.57  #    Propositional check unsatisfiable : 0
% 11.36/11.57  #    Propositional clauses             : 0
% 11.36/11.57  #    Propositional clauses after purity: 0
% 11.36/11.57  #    Propositional unsat core size     : 0
% 11.36/11.57  #    Propositional preprocessing time  : 0.000
% 11.36/11.57  #    Propositional encoding time       : 0.000
% 11.36/11.57  #    Propositional solver time         : 0.000
% 11.36/11.57  #    Success case prop preproc time    : 0.000
% 11.36/11.57  #    Success case prop encoding time   : 0.000
% 11.36/11.57  #    Success case prop solver time     : 0.000
% 11.36/11.57  # Current number of processed clauses  : 1354
% 11.36/11.57  #    Positive orientable unit clauses  : 29
% 11.36/11.57  #    Positive unorientable unit clauses: 0
% 11.36/11.57  #    Negative unit clauses             : 0
% 11.36/11.57  #    Non-unit-clauses                  : 1325
% 11.36/11.57  # Current number of unprocessed clauses: 1175289
% 11.36/11.57  # ...number of literals in the above   : 8636479
% 11.36/11.57  # Current number of archived formulas  : 0
% 11.36/11.57  # Current number of archived clauses   : 1075
% 11.36/11.57  # Clause-clause subsumption calls (NU) : 1043968
% 11.36/11.57  # Rec. Clause-clause subsumption calls : 593070
% 11.36/11.57  # Non-unit clause-clause subsumptions  : 18316
% 11.36/11.57  # Unit Clause-clause subsumption calls : 5387
% 11.36/11.57  # Rewrite failures with RHS unbound    : 0
% 11.36/11.57  # BW rewrite match attempts            : 620
% 11.36/11.57  # BW rewrite match successes           : 51
% 11.36/11.57  # Condensation attempts                : 0
% 11.36/11.57  # Condensation successes               : 0
% 11.36/11.57  # Termbank termtop insertions          : 48313027
% 11.45/11.62  
% 11.45/11.62  # -------------------------------------------------
% 11.45/11.62  # User time                : 10.811 s
% 11.45/11.62  # System time              : 0.485 s
% 11.45/11.62  # Total time               : 11.296 s
% 11.45/11.62  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
