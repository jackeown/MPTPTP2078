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
% DateTime   : Thu Dec  3 11:01:06 EST 2020

% Result     : Theorem 18.19s
% Output     : CNFRefutation 18.19s
% Verified   : 
% Statistics : Number of formulae       :  191 (56671 expanded)
%              Number of clauses        :  170 (27134 expanded)
%              Number of leaves         :   10 (13883 expanded)
%              Depth                    :   35
%              Number of atoms          :  499 (182038 expanded)
%              Number of equality atoms :  100 (79853 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t4_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(c_0_10,plain,(
    ! [X10,X11] :
      ( ( k2_zfmisc_1(X10,X11) != k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r1_tarski(k2_relat_1(X2),X1)
         => ( v1_funct_1(X2)
            & v1_funct_2(X2,k1_relat_1(X2),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t4_funct_2])).

cnf(c_0_12,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_14,plain,(
    ! [X9] : r1_tarski(k1_xboole_0,X9) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_15,plain,(
    ! [X17] :
      ( ~ v1_relat_1(X17)
      | r1_tarski(X17,k2_zfmisc_1(k1_relat_1(X17),k2_relat_1(X17))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & r1_tarski(k2_relat_1(esk2_0),esk1_0)
    & ( ~ v1_funct_1(esk2_0)
      | ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_17,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_22,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_23,plain,(
    ! [X12,X13,X14] :
      ( ( r1_tarski(k2_zfmisc_1(X12,X14),k2_zfmisc_1(X13,X14))
        | ~ r1_tarski(X12,X13) )
      & ( r1_tarski(k2_zfmisc_1(X14,X12),k2_zfmisc_1(X14,X13))
        | ~ r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | k2_zfmisc_1(X1,X1) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_19]),c_0_21]),c_0_19])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_funct_1(esk2_0)
    | ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_33,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_35,plain,
    ( k2_zfmisc_1(X1,X2) = X2
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_20]),c_0_21])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X1,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r1_tarski(X1,k2_zfmisc_1(X4,X3))
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk2_0,k2_relat_1(esk2_0))
    | ~ r1_tarski(k2_relat_1(esk2_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk1_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X4))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(X1,k2_relat_1(esk2_0)))
    | ~ r1_tarski(k1_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_34])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
    | ~ r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(X1,esk1_0)
    | ~ r1_tarski(X1,k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_36])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk2_0,k2_relat_1(esk2_0))
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk1_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_50,plain,(
    ! [X21,X22,X23] :
      ( ( ~ v1_funct_2(X23,X21,X22)
        | X21 = k1_relset_1(X21,X22,X23)
        | X22 = k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( X21 != k1_relset_1(X21,X22,X23)
        | v1_funct_2(X23,X21,X22)
        | X22 = k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( ~ v1_funct_2(X23,X21,X22)
        | X21 = k1_relset_1(X21,X22,X23)
        | X21 != k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( X21 != k1_relset_1(X21,X22,X23)
        | v1_funct_2(X23,X21,X22)
        | X21 != k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( ~ v1_funct_2(X23,X21,X22)
        | X23 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 != k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( X23 != k1_xboole_0
        | v1_funct_2(X23,X21,X22)
        | X21 = k1_xboole_0
        | X22 != k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(X1,X2))
    | ~ r1_tarski(k2_relat_1(esk2_0),X2)
    | ~ r1_tarski(k1_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),esk1_0)
    | ~ r1_tarski(esk2_0,X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_20])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( ~ v1_funct_2(X1,k1_relat_1(X1),esk1_0)
    | ~ r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),esk1_0))
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_20])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0)
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk1_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(X1,esk1_0))
    | ~ r1_tarski(k1_relat_1(esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_58,negated_conjecture,
    ( ~ v1_funct_2(X1,X2,esk1_0)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,esk1_0))
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_20])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),X1))
    | ~ r1_tarski(k2_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_34])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0)
    | ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),k2_zfmisc_1(esk1_0,esk1_0)),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_37]),c_0_21])])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relset_1(X3,X1,X2) != X3
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_41])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_53]),c_0_53]),c_0_36])])).

fof(c_0_64,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | k1_relset_1(X18,X19,X20) = k1_relat_1(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk2_0,k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(esk2_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_28]),c_0_26])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_28])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0)
    | ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),k2_zfmisc_1(esk1_0,esk1_0)),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),k2_zfmisc_1(esk1_0,esk1_0))),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_37]),c_0_21])])).

cnf(c_0_68,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | k1_relset_1(k1_relat_1(esk2_0),esk1_0,esk2_0) != k1_relat_1(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_69,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0),k1_xboole_0)
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_28])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(esk2_0,k1_xboole_0)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0)
    | ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),k2_zfmisc_1(esk1_0,esk1_0)),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),k2_zfmisc_1(esk1_0,esk1_0))),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),k2_zfmisc_1(esk1_0,esk1_0)),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),k2_zfmisc_1(esk1_0,esk1_0)))),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_37]),c_0_21])])).

cnf(c_0_73,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_35]),c_0_71])).

cnf(c_0_75,plain,
    ( X1 = X2
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_28])).

cnf(c_0_76,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 = k1_xboole_0
    | X1 != k1_xboole_0
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(esk2_0,k1_xboole_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_21])])).

cnf(c_0_78,negated_conjecture,
    ( ~ v1_funct_2(X1,k1_relat_1(X1),esk1_0)
    | ~ r1_tarski(esk1_0,k1_xboole_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_71])).

cnf(c_0_79,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_76])]),c_0_26])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_20]),c_0_21])])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_41]),c_0_62])])).

cnf(c_0_82,negated_conjecture,
    ( ~ v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(esk1_0,X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_75])).

cnf(c_0_83,plain,
    ( v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | r1_tarski(X1,X2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),k1_xboole_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_73]),c_0_21])])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_86,plain,
    ( k2_zfmisc_1(X1,X2) = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(esk2_0,k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(esk2_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_28]),c_0_19])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_21]),c_0_21])])).

cnf(c_0_89,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_41]),c_0_85])])).

cnf(c_0_90,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
    | ~ r1_tarski(k1_relat_1(esk2_0),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_86]),c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_41]),c_0_21])])).

cnf(c_0_92,negated_conjecture,
    ( v1_relat_1(X1)
    | ~ r1_tarski(esk2_0,X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_20])).

cnf(c_0_93,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X4,X2))
    | ~ r1_tarski(k2_zfmisc_1(X4,X2),X3)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_94,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_19])).

cnf(c_0_95,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_20]),c_0_21])])).

cnf(c_0_96,plain,
    ( v1_funct_2(X1,X2,X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_20]),c_0_21])])).

cnf(c_0_97,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_xboole_0,esk1_0)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),k1_relat_1(esk2_0)),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_37]),c_0_21])])).

cnf(c_0_98,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,X1,esk1_0)
    | ~ r1_tarski(k1_relat_1(esk2_0),k1_xboole_0)
    | ~ r1_tarski(X1,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_75])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(esk1_0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_20]),c_0_21])])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(k2_relat_1(esk2_0),X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_20]),c_0_21])])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ r1_tarski(esk2_0,X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_92])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk2_0)),esk2_0)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)),esk2_0)
    | ~ r1_tarski(X1,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_34])).

cnf(c_0_103,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),X3)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_94])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk2_0),X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_85])])).

cnf(c_0_105,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,X1,esk1_0)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),k1_relat_1(esk2_0)),X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_20]),c_0_21])])).

cnf(c_0_106,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_34])).

cnf(c_0_107,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,X1,esk1_0)
    | ~ r1_tarski(X1,k1_relat_1(esk2_0))
    | ~ r1_tarski(esk1_0,esk2_0)
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(k2_relat_1(esk2_0)),k2_relat_1(k2_relat_1(esk2_0))))
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(k2_relat_1(esk2_0)),k2_relat_1(k2_relat_1(esk2_0))),k1_xboole_0)
    | ~ r1_tarski(esk2_0,k2_relat_1(esk2_0))
    | ~ r1_tarski(k2_relat_1(esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_109,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk2_0)),esk2_0)
    | ~ r1_tarski(k1_relat_1(esk2_0),X2)
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_75]),c_0_103])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_41]),c_0_53])])).

cnf(c_0_111,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)),esk1_0)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)),k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),k1_relat_1(esk2_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_112,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,X1,esk1_0)
    | ~ r1_tarski(X1,k1_relat_1(k1_xboole_0))
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_28]),c_0_21])]),c_0_71])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(esk2_0,k1_relat_1(k2_relat_1(esk2_0)))
    | ~ r1_tarski(k1_relat_1(k2_relat_1(esk2_0)),k1_xboole_0)
    | ~ r1_tarski(esk2_0,k2_relat_1(esk2_0))
    | ~ r1_tarski(k2_relat_1(esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_86])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),X1)
    | ~ r1_tarski(esk1_0,X1)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_20])).

cnf(c_0_115,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_20])]),c_0_21])])).

cnf(c_0_116,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk2_0)),esk2_0)
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_110])])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_73])).

cnf(c_0_118,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),esk1_0)
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_21]),c_0_21])])).

cnf(c_0_119,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_xboole_0,esk1_0)
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),k1_relat_1(esk2_0)),esk2_0)
    | ~ r1_tarski(k2_zfmisc_1(k2_relat_1(esk2_0),k2_relat_1(esk2_0)),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_37]),c_0_26]),c_0_26]),c_0_21])])).

cnf(c_0_120,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),X3)
    | ~ r1_tarski(X3,k1_xboole_0)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_35])).

cnf(c_0_121,negated_conjecture,
    ( r1_tarski(esk2_0,k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(k2_relat_1(esk2_0),k2_relat_1(esk2_0)),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_37]),c_0_26])).

cnf(c_0_122,negated_conjecture,
    ( k2_relat_1(esk2_0) = k1_xboole_0
    | v1_funct_2(esk2_0,k1_relat_1(esk2_0),k2_relat_1(esk2_0))
    | k1_relset_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0),esk2_0) != k1_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_34])).

cnf(c_0_123,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | ~ r1_tarski(X1,k1_relat_1(k1_xboole_0))
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_28]),c_0_21])])).

cnf(c_0_124,negated_conjecture,
    ( r1_tarski(esk2_0,k1_relat_1(k2_relat_1(esk2_0)))
    | ~ r1_tarski(esk1_0,k2_relat_1(esk2_0))
    | ~ r1_tarski(k2_relat_1(esk2_0),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_99]),c_0_80]),c_0_42])).

cnf(c_0_125,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),X1)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_114]),c_0_21])])).

cnf(c_0_126,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_75]),c_0_103])).

cnf(c_0_127,plain,
    ( X1 = X2
    | X3 = X2
    | ~ r1_tarski(k2_zfmisc_1(X3,X1),X2)
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_20]),c_0_21])])).

cnf(c_0_128,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk2_0)),esk2_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_85])).

cnf(c_0_129,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_41]),c_0_85])])).

cnf(c_0_130,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X1)
    | ~ r1_tarski(esk1_0,k1_xboole_0)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_75]),c_0_71])).

cnf(c_0_131,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_xboole_0,esk1_0)
    | ~ r1_tarski(k2_zfmisc_1(k2_relat_1(esk2_0),k2_relat_1(esk2_0)),k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_121])).

cnf(c_0_132,negated_conjecture,
    ( k2_relat_1(esk2_0) = k1_xboole_0
    | v1_funct_2(esk2_0,k1_relat_1(esk2_0),k2_relat_1(esk2_0))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_122,c_0_69])).

cnf(c_0_133,negated_conjecture,
    ( ~ v1_funct_2(X1,X2,X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(esk1_0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_20]),c_0_21])])).

cnf(c_0_134,negated_conjecture,
    ( r1_tarski(esk2_0,k1_relat_1(k1_xboole_0))
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_28]),c_0_21])]),c_0_125])).

cnf(c_0_135,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),esk1_0)
    | ~ r1_tarski(X1,k2_zfmisc_1(esk2_0,X2))
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_126])).

cnf(c_0_136,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk2_0)),esk2_0)
    | ~ r1_tarski(k1_relat_1(esk2_0),k1_xboole_0)
    | ~ r1_tarski(X1,k1_relat_1(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_86]),c_0_80])).

cnf(c_0_137,negated_conjecture,
    ( k2_relat_1(esk2_0) = esk2_0
    | X1 = esk2_0
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_85])])).

cnf(c_0_138,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_129])).

cnf(c_0_139,negated_conjecture,
    ( ~ v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(esk1_0,X1)
    | ~ r1_tarski(X2,esk1_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_20]),c_0_21])])).

cnf(c_0_140,negated_conjecture,
    ( v1_funct_2(esk2_0,k1_relat_1(esk2_0),k2_relat_1(esk2_0))
    | ~ v1_funct_2(esk2_0,k1_xboole_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0))))
    | ~ r1_tarski(k1_relat_1(esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_19]),c_0_21])])).

cnf(c_0_141,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_134]),c_0_21])])).

cnf(c_0_142,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),esk1_0)
    | ~ r1_tarski(X1,k2_zfmisc_1(esk2_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_135,c_0_81])])).

cnf(c_0_143,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk2_0)),esk2_0)
    | ~ r1_tarski(X1,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_136,c_0_110])])).

cnf(c_0_144,negated_conjecture,
    ( k2_relat_1(esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_137]),c_0_138])])).

cnf(c_0_145,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_xboole_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0))))
    | ~ r1_tarski(esk1_0,esk2_0)
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_36])]),c_0_99])).

cnf(c_0_146,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_141,c_0_83])).

cnf(c_0_147,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_relat_1(esk2_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_142,c_0_110])).

cnf(c_0_148,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,esk2_0),esk2_0)
    | ~ r1_tarski(X1,k1_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_143,c_0_144])).

cnf(c_0_149,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_xboole_0,esk1_0)
    | ~ r1_tarski(esk1_0,esk2_0)
    | ~ r1_tarski(esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_41]),c_0_34])])).

cnf(c_0_150,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_41]),c_0_21])])).

cnf(c_0_151,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),X3)
    | ~ r1_tarski(X3,k1_xboole_0)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_86])).

cnf(c_0_152,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_relat_1(esk2_0)),k1_xboole_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(spm,[status(thm)],[c_0_147,c_0_73])).

cnf(c_0_153,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X2,X1),X3)
    | ~ r1_tarski(X3,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_20]),c_0_80])).

cnf(c_0_154,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk2_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_148,c_0_85])).

cnf(c_0_155,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_28]),c_0_85])])).

cnf(c_0_156,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_28]),c_0_21])]),c_0_150])).

cnf(c_0_157,plain,
    ( X1 = X2
    | ~ r1_tarski(k2_zfmisc_1(X2,X2),k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_37])).

cnf(c_0_158,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,X2),esk1_0)
    | ~ r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)
    | ~ r1_tarski(X1,k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_151])).

cnf(c_0_159,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_relat_1(esk2_0)),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_41]),c_0_85])])).

cnf(c_0_160,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_154]),c_0_85])])).

cnf(c_0_161,negated_conjecture,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_155,c_0_83])).

cnf(c_0_162,negated_conjecture,
    ( ~ v1_funct_2(X1,k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(X1,X1),k1_xboole_0)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_157]),c_0_150])).

cnf(c_0_163,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,X2),esk1_0)
    | ~ r1_tarski(X1,k2_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_158,c_0_129])])).

cnf(c_0_164,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_relat_1(esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_159])).

cnf(c_0_165,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | k1_relset_1(k1_relat_1(k1_xboole_0),esk1_0,k1_xboole_0) != k1_relat_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_160]),c_0_160]),c_0_160])).

cnf(c_0_166,negated_conjecture,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_41]),c_0_21])])).

cnf(c_0_167,negated_conjecture,
    ( ~ v1_funct_2(X1,X2,X2)
    | ~ r1_tarski(k2_zfmisc_1(X1,X1),X2)
    | ~ r1_tarski(esk1_0,X2)
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_20]),c_0_21])])).

cnf(c_0_168,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k2_relat_1(k1_relat_1(esk2_0)),X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_163,c_0_164])).

cnf(c_0_169,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | k1_relset_1(k1_xboole_0,esk1_0,k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_28]),c_0_166])])).

cnf(c_0_170,negated_conjecture,
    ( ~ v1_funct_2(k2_relat_1(k1_relat_1(esk2_0)),esk1_0,esk1_0)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_168]),c_0_53])])).

cnf(c_0_171,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_69]),c_0_19])).

cnf(c_0_172,negated_conjecture,
    ( ~ v1_funct_2(k2_relat_1(k1_relat_1(esk2_0)),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_73]),c_0_21])])).

cnf(c_0_173,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_174,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_163,c_0_166])).

cnf(c_0_175,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_41]),c_0_21])])).

cnf(c_0_176,negated_conjecture,
    ( ~ v1_funct_2(k2_relat_1(k1_relat_1(esk2_0)),k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_172,c_0_41]),c_0_85])])).

cnf(c_0_177,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_173]),c_0_19])).

cnf(c_0_178,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) = esk1_0
    | X1 = esk1_0
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_127,c_0_174])).

cnf(c_0_179,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175,c_0_28]),c_0_166])])).

cnf(c_0_180,negated_conjecture,
    ( ~ v1_funct_2(k2_relat_1(k1_relat_1(k1_xboole_0)),k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_28]),c_0_85])])).

cnf(c_0_181,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_177,c_0_41])).

cnf(c_0_182,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | X1 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_178,c_0_179]),c_0_179]),c_0_179]),c_0_21])])).

cnf(c_0_183,negated_conjecture,
    ( ~ v1_funct_2(k2_relat_1(k1_relat_1(X1)),X1,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180,c_0_20]),c_0_21])])).

cnf(c_0_184,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | ~ r1_tarski(k1_relset_1(k1_xboole_0,X2,X1),k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_181,c_0_28])).

cnf(c_0_185,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_182])).

cnf(c_0_186,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_28]),c_0_85])])).

cnf(c_0_187,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_relat_1(k1_xboole_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_28]),c_0_85])])).

cnf(c_0_188,negated_conjecture,
    ( ~ r1_tarski(k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183,c_0_184]),c_0_21]),c_0_185]),c_0_186]),c_0_187])])).

cnf(c_0_189,negated_conjecture,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_188,c_0_69]),c_0_166]),c_0_19])])).

cnf(c_0_190,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189,c_0_41]),c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:40:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 18.19/18.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 18.19/18.37  # and selection function PSelectUnlessUniqMaxPos.
% 18.19/18.37  #
% 18.19/18.37  # Preprocessing time       : 0.027 s
% 18.19/18.37  # Presaturation interreduction done
% 18.19/18.37  
% 18.19/18.37  # Proof found!
% 18.19/18.37  # SZS status Theorem
% 18.19/18.37  # SZS output start CNFRefutation
% 18.19/18.37  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 18.19/18.37  fof(t4_funct_2, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 18.19/18.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.19/18.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 18.19/18.37  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 18.19/18.37  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 18.19/18.37  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 18.19/18.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 18.19/18.37  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 18.19/18.37  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 18.19/18.37  fof(c_0_10, plain, ![X10, X11]:((k2_zfmisc_1(X10,X11)!=k1_xboole_0|(X10=k1_xboole_0|X11=k1_xboole_0))&((X10!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0)&(X11!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 18.19/18.37  fof(c_0_11, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))))))), inference(assume_negation,[status(cth)],[t4_funct_2])).
% 18.19/18.37  cnf(c_0_12, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 18.19/18.37  fof(c_0_13, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 18.19/18.37  fof(c_0_14, plain, ![X9]:r1_tarski(k1_xboole_0,X9), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 18.19/18.37  fof(c_0_15, plain, ![X17]:(~v1_relat_1(X17)|r1_tarski(X17,k2_zfmisc_1(k1_relat_1(X17),k2_relat_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 18.19/18.37  fof(c_0_16, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&(r1_tarski(k2_relat_1(esk2_0),esk1_0)&(~v1_funct_1(esk2_0)|~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 18.19/18.37  cnf(c_0_17, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 18.19/18.37  cnf(c_0_18, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 18.19/18.37  cnf(c_0_19, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_12])).
% 18.19/18.37  cnf(c_0_20, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 18.19/18.37  cnf(c_0_21, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 18.19/18.37  fof(c_0_22, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 18.19/18.37  fof(c_0_23, plain, ![X12, X13, X14]:((r1_tarski(k2_zfmisc_1(X12,X14),k2_zfmisc_1(X13,X14))|~r1_tarski(X12,X13))&(r1_tarski(k2_zfmisc_1(X14,X12),k2_zfmisc_1(X14,X13))|~r1_tarski(X12,X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 18.19/18.37  cnf(c_0_24, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 18.19/18.37  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 18.19/18.37  cnf(c_0_26, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_17])).
% 18.19/18.37  cnf(c_0_27, plain, (X1=k1_xboole_0|k2_zfmisc_1(X1,X1)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_18])).
% 18.19/18.37  cnf(c_0_28, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_19]), c_0_21]), c_0_19])])).
% 18.19/18.37  cnf(c_0_29, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 18.19/18.37  cnf(c_0_30, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 18.19/18.37  cnf(c_0_31, negated_conjecture, (~v1_funct_1(esk2_0)|~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 18.19/18.37  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 18.19/18.37  fof(c_0_33, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 18.19/18.37  cnf(c_0_34, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 18.19/18.37  cnf(c_0_35, plain, (k2_zfmisc_1(X1,X2)=X2|~r1_tarski(X2,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_20]), c_0_21])])).
% 18.19/18.37  cnf(c_0_36, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 18.19/18.37  cnf(c_0_37, plain, (X1=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X1,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 18.19/18.37  cnf(c_0_38, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 18.19/18.37  cnf(c_0_39, plain, (r1_tarski(X1,k2_zfmisc_1(X2,X3))|~r1_tarski(X1,k2_zfmisc_1(X4,X3))|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 18.19/18.37  cnf(c_0_40, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32])])).
% 18.19/18.37  cnf(c_0_41, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 18.19/18.37  cnf(c_0_42, negated_conjecture, (r1_tarski(esk2_0,k2_relat_1(esk2_0))|~r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 18.19/18.37  cnf(c_0_43, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)|~r1_tarski(k2_zfmisc_1(esk1_0,esk1_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 18.19/18.37  cnf(c_0_44, plain, (r1_tarski(X1,k2_zfmisc_1(X2,X3))|~r1_tarski(X1,k2_zfmisc_1(X2,X4))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_29, c_0_38])).
% 18.19/18.37  cnf(c_0_45, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(X1,k2_relat_1(esk2_0)))|~r1_tarski(k1_relat_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_39, c_0_34])).
% 18.19/18.37  cnf(c_0_46, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 18.19/18.37  cnf(c_0_47, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)|~r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 18.19/18.37  cnf(c_0_48, negated_conjecture, (r1_tarski(X1,esk1_0)|~r1_tarski(X1,k2_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_29, c_0_36])).
% 18.19/18.37  cnf(c_0_49, negated_conjecture, (r1_tarski(esk2_0,k2_relat_1(esk2_0))|~r1_tarski(k2_zfmisc_1(esk1_0,esk1_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 18.19/18.37  fof(c_0_50, plain, ![X21, X22, X23]:((((~v1_funct_2(X23,X21,X22)|X21=k1_relset_1(X21,X22,X23)|X22=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))&(X21!=k1_relset_1(X21,X22,X23)|v1_funct_2(X23,X21,X22)|X22=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))))&((~v1_funct_2(X23,X21,X22)|X21=k1_relset_1(X21,X22,X23)|X21!=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))&(X21!=k1_relset_1(X21,X22,X23)|v1_funct_2(X23,X21,X22)|X21!=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))))&((~v1_funct_2(X23,X21,X22)|X23=k1_xboole_0|X21=k1_xboole_0|X22!=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))&(X23!=k1_xboole_0|v1_funct_2(X23,X21,X22)|X21=k1_xboole_0|X22!=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 18.19/18.37  cnf(c_0_51, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(X1,X2))|~r1_tarski(k2_relat_1(esk2_0),X2)|~r1_tarski(k1_relat_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 18.19/18.37  cnf(c_0_52, negated_conjecture, (r1_tarski(k2_relat_1(X1),esk1_0)|~r1_tarski(esk2_0,X1)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_36, c_0_20])).
% 18.19/18.37  cnf(c_0_53, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_46])).
% 18.19/18.37  cnf(c_0_54, negated_conjecture, (~v1_funct_2(X1,k1_relat_1(X1),esk1_0)|~r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),esk1_0))|~r1_tarski(X1,esk2_0)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_47, c_0_20])).
% 18.19/18.37  cnf(c_0_55, negated_conjecture, (r1_tarski(esk2_0,esk1_0)|~r1_tarski(k2_zfmisc_1(esk1_0,esk1_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 18.19/18.37  cnf(c_0_56, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 18.19/18.37  cnf(c_0_57, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(X1,esk1_0))|~r1_tarski(k1_relat_1(esk2_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 18.19/18.37  cnf(c_0_58, negated_conjecture, (~v1_funct_2(X1,X2,esk1_0)|~r1_tarski(X1,k2_zfmisc_1(X2,esk1_0))|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(X1,esk2_0)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_54, c_0_20])).
% 18.19/18.37  cnf(c_0_59, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),X1))|~r1_tarski(k2_relat_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_44, c_0_34])).
% 18.19/18.37  cnf(c_0_60, negated_conjecture, (r1_tarski(esk2_0,esk1_0)|~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),k2_zfmisc_1(esk1_0,esk1_0)),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_37]), c_0_21])])).
% 18.19/18.37  cnf(c_0_61, plain, (X1=k1_xboole_0|v1_funct_2(X2,X3,X1)|k1_relset_1(X3,X1,X2)!=X3|~r1_tarski(X2,k2_zfmisc_1(X3,X1))), inference(spm,[status(thm)],[c_0_56, c_0_41])).
% 18.19/18.37  cnf(c_0_62, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))), inference(spm,[status(thm)],[c_0_57, c_0_53])).
% 18.19/18.37  cnf(c_0_63, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_53]), c_0_53]), c_0_36])])).
% 18.19/18.37  fof(c_0_64, plain, ![X18, X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|k1_relset_1(X18,X19,X20)=k1_relat_1(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 18.19/18.37  cnf(c_0_65, negated_conjecture, (r1_tarski(esk2_0,k1_xboole_0)|~r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_28]), c_0_26])).
% 18.19/18.37  cnf(c_0_66, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_28])).
% 18.19/18.37  cnf(c_0_67, negated_conjecture, (r1_tarski(esk2_0,esk1_0)|~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),k2_zfmisc_1(esk1_0,esk1_0)),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),k2_zfmisc_1(esk1_0,esk1_0))),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_37]), c_0_21])])).
% 18.19/18.37  cnf(c_0_68, negated_conjecture, (esk1_0=k1_xboole_0|k1_relset_1(k1_relat_1(esk2_0),esk1_0,esk2_0)!=k1_relat_1(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 18.19/18.37  cnf(c_0_69, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 18.19/18.37  cnf(c_0_70, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)|~r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0),k1_xboole_0)|~r1_tarski(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_28])).
% 18.19/18.37  cnf(c_0_71, negated_conjecture, (r1_tarski(esk2_0,k1_xboole_0)|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 18.19/18.37  cnf(c_0_72, negated_conjecture, (r1_tarski(esk2_0,esk1_0)|~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),k2_zfmisc_1(esk1_0,esk1_0)),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),k2_zfmisc_1(esk1_0,esk1_0))),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),k2_zfmisc_1(esk1_0,esk1_0)),k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0),k2_zfmisc_1(esk1_0,esk1_0)))),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_37]), c_0_21])])).
% 18.19/18.37  cnf(c_0_73, negated_conjecture, (esk1_0=k1_xboole_0|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 18.19/18.37  cnf(c_0_74, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)|~r1_tarski(esk1_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_35]), c_0_71])).
% 18.19/18.37  cnf(c_0_75, plain, (X1=X2|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_28])).
% 18.19/18.37  cnf(c_0_76, plain, (v1_funct_2(X1,X2,X3)|X2=k1_xboole_0|X1!=k1_xboole_0|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 18.19/18.37  cnf(c_0_77, negated_conjecture, (r1_tarski(esk2_0,k1_xboole_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_21])])).
% 18.19/18.37  cnf(c_0_78, negated_conjecture, (~v1_funct_2(X1,k1_relat_1(X1),esk1_0)|~r1_tarski(esk1_0,k1_xboole_0)|~r1_tarski(X1,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_71])).
% 18.19/18.37  cnf(c_0_79, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,X1,k1_xboole_0)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_76])]), c_0_26])).
% 18.19/18.37  cnf(c_0_80, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_20]), c_0_21])])).
% 18.19/18.37  cnf(c_0_81, negated_conjecture, (r1_tarski(esk2_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_41]), c_0_62])])).
% 18.19/18.37  cnf(c_0_82, negated_conjecture, (~v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(X1,esk2_0)|~r1_tarski(esk1_0,X2)), inference(spm,[status(thm)],[c_0_78, c_0_75])).
% 18.19/18.37  cnf(c_0_83, plain, (v1_funct_2(k1_xboole_0,X1,k1_xboole_0)|r1_tarski(X1,X2)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_21, c_0_79])).
% 18.19/18.37  cnf(c_0_84, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(esk2_0),k1_xboole_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_73]), c_0_21])])).
% 18.19/18.37  cnf(c_0_85, negated_conjecture, (r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 18.19/18.37  cnf(c_0_86, plain, (k2_zfmisc_1(X1,X2)=X1|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 18.19/18.37  cnf(c_0_87, negated_conjecture, (r1_tarski(esk2_0,k1_xboole_0)|~r1_tarski(k1_relat_1(esk2_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_28]), c_0_19])).
% 18.19/18.37  cnf(c_0_88, negated_conjecture, (r1_tarski(k1_relat_1(k1_xboole_0),X1)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(esk1_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_21]), c_0_21])])).
% 18.19/18.37  cnf(c_0_89, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(esk2_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_41]), c_0_85])])).
% 18.19/18.37  cnf(c_0_90, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)|~r1_tarski(k1_relat_1(esk2_0),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_86]), c_0_87])).
% 18.19/18.37  cnf(c_0_91, negated_conjecture, (r1_tarski(k1_relat_1(k1_xboole_0),X1)|~r1_tarski(esk1_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_41]), c_0_21])])).
% 18.19/18.37  cnf(c_0_92, negated_conjecture, (v1_relat_1(X1)|~r1_tarski(esk2_0,X1)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_25, c_0_20])).
% 18.19/18.37  cnf(c_0_93, plain, (r1_tarski(k2_zfmisc_1(X1,X2),X3)|~r1_tarski(X3,k2_zfmisc_1(X4,X2))|~r1_tarski(k2_zfmisc_1(X4,X2),X3)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_30, c_0_20])).
% 18.19/18.37  cnf(c_0_94, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_19])).
% 18.19/18.37  cnf(c_0_95, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(esk2_0),X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_20]), c_0_21])])).
% 18.19/18.37  cnf(c_0_96, plain, (v1_funct_2(X1,X2,X1)|r1_tarski(X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(X1))|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_20]), c_0_21])])).
% 18.19/18.37  cnf(c_0_97, negated_conjecture, (~v1_funct_2(esk2_0,k1_xboole_0,esk1_0)|~r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),k1_relat_1(esk2_0)),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_37]), c_0_21])])).
% 18.19/18.37  cnf(c_0_98, negated_conjecture, (~v1_funct_2(esk2_0,X1,esk1_0)|~r1_tarski(k1_relat_1(esk2_0),k1_xboole_0)|~r1_tarski(X1,k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_63, c_0_75])).
% 18.19/18.37  cnf(c_0_99, negated_conjecture, (r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(esk1_0,X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_20]), c_0_21])])).
% 18.19/18.37  cnf(c_0_100, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(k2_relat_1(esk2_0),X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_20]), c_0_21])])).
% 18.19/18.37  cnf(c_0_101, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~r1_tarski(esk2_0,X1)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_24, c_0_92])).
% 18.19/18.37  cnf(c_0_102, negated_conjecture, (r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk2_0)),esk2_0)|~r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)),esk2_0)|~r1_tarski(X1,k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_93, c_0_34])).
% 18.19/18.37  cnf(c_0_103, plain, (r1_tarski(k2_zfmisc_1(X1,X2),X3)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_80, c_0_94])).
% 18.19/18.37  cnf(c_0_104, negated_conjecture, (r1_tarski(k1_relat_1(esk2_0),X1)|~m1_subset_1(esk2_0,k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_85])])).
% 18.19/18.37  cnf(c_0_105, negated_conjecture, (~v1_funct_2(esk2_0,X1,esk1_0)|~r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),k1_relat_1(esk2_0)),X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_20]), c_0_21])])).
% 18.19/18.37  cnf(c_0_106, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_34])).
% 18.19/18.37  cnf(c_0_107, negated_conjecture, (~v1_funct_2(esk2_0,X1,esk1_0)|~r1_tarski(X1,k1_relat_1(esk2_0))|~r1_tarski(esk1_0,esk2_0)|~r1_tarski(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 18.19/18.37  cnf(c_0_108, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(k2_relat_1(esk2_0)),k2_relat_1(k2_relat_1(esk2_0))))|~r1_tarski(k2_zfmisc_1(k1_relat_1(k2_relat_1(esk2_0)),k2_relat_1(k2_relat_1(esk2_0))),k1_xboole_0)|~r1_tarski(esk2_0,k2_relat_1(esk2_0))|~r1_tarski(k2_relat_1(esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 18.19/18.37  cnf(c_0_109, negated_conjecture, (r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk2_0)),esk2_0)|~r1_tarski(k1_relat_1(esk2_0),X2)|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_75]), c_0_103])).
% 18.19/18.37  cnf(c_0_110, negated_conjecture, (r1_tarski(k1_relat_1(esk2_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_41]), c_0_53])])).
% 18.19/18.37  cnf(c_0_111, negated_conjecture, (~v1_funct_2(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)),esk1_0)|~r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)),k1_xboole_0)|~r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),k1_relat_1(esk2_0)),esk2_0)), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 18.19/18.37  cnf(c_0_112, negated_conjecture, (~v1_funct_2(k1_xboole_0,X1,esk1_0)|~r1_tarski(X1,k1_relat_1(k1_xboole_0))|~r1_tarski(esk1_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_28]), c_0_21])]), c_0_71])).
% 18.19/18.37  cnf(c_0_113, negated_conjecture, (r1_tarski(esk2_0,k1_relat_1(k2_relat_1(esk2_0)))|~r1_tarski(k1_relat_1(k2_relat_1(esk2_0)),k1_xboole_0)|~r1_tarski(esk2_0,k2_relat_1(esk2_0))|~r1_tarski(k2_relat_1(esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_108, c_0_86])).
% 18.19/18.37  cnf(c_0_114, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),X1)|~r1_tarski(esk1_0,X1)|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_36, c_0_20])).
% 18.19/18.37  cnf(c_0_115, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_20])]), c_0_21])])).
% 18.19/18.37  cnf(c_0_116, negated_conjecture, (r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk2_0)),esk2_0)|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_110])])).
% 18.19/18.37  cnf(c_0_117, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(spm,[status(thm)],[c_0_36, c_0_73])).
% 18.19/18.37  cnf(c_0_118, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),esk1_0)|~r1_tarski(esk2_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_21]), c_0_21])])).
% 18.19/18.37  cnf(c_0_119, negated_conjecture, (~v1_funct_2(esk2_0,k1_xboole_0,esk1_0)|~r1_tarski(k2_zfmisc_1(k1_relat_1(esk2_0),k1_relat_1(esk2_0)),esk2_0)|~r1_tarski(k2_zfmisc_1(k2_relat_1(esk2_0),k2_relat_1(esk2_0)),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_37]), c_0_26]), c_0_26]), c_0_21])])).
% 18.19/18.37  cnf(c_0_120, plain, (r1_tarski(k2_zfmisc_1(X1,X2),X3)|~r1_tarski(X3,k1_xboole_0)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_38, c_0_35])).
% 18.19/18.37  cnf(c_0_121, negated_conjecture, (r1_tarski(esk2_0,k1_xboole_0)|~r1_tarski(k2_zfmisc_1(k2_relat_1(esk2_0),k2_relat_1(esk2_0)),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_37]), c_0_26])).
% 18.19/18.37  cnf(c_0_122, negated_conjecture, (k2_relat_1(esk2_0)=k1_xboole_0|v1_funct_2(esk2_0,k1_relat_1(esk2_0),k2_relat_1(esk2_0))|k1_relset_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0),esk2_0)!=k1_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_61, c_0_34])).
% 18.19/18.37  cnf(c_0_123, negated_conjecture, (~v1_funct_2(k1_xboole_0,X1,k1_xboole_0)|~r1_tarski(X1,k1_relat_1(k1_xboole_0))|~r1_tarski(esk1_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_28]), c_0_21])])).
% 18.19/18.37  cnf(c_0_124, negated_conjecture, (r1_tarski(esk2_0,k1_relat_1(k2_relat_1(esk2_0)))|~r1_tarski(esk1_0,k2_relat_1(esk2_0))|~r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_99]), c_0_80]), c_0_42])).
% 18.19/18.37  cnf(c_0_125, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),X1)|~r1_tarski(esk1_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_114]), c_0_21])])).
% 18.19/18.37  cnf(c_0_126, plain, (X1=X2|~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~r1_tarski(X2,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_75]), c_0_103])).
% 18.19/18.37  cnf(c_0_127, plain, (X1=X2|X3=X2|~r1_tarski(k2_zfmisc_1(X3,X1),X2)|~r1_tarski(X2,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_20]), c_0_21])])).
% 18.19/18.37  cnf(c_0_128, negated_conjecture, (r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk2_0)),esk2_0)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_116, c_0_85])).
% 18.19/18.37  cnf(c_0_129, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_41]), c_0_85])])).
% 18.19/18.37  cnf(c_0_130, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X1)|~r1_tarski(esk1_0,k1_xboole_0)|~r1_tarski(X1,esk1_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_75]), c_0_71])).
% 18.19/18.37  cnf(c_0_131, negated_conjecture, (~v1_funct_2(esk2_0,k1_xboole_0,esk1_0)|~r1_tarski(k2_zfmisc_1(k2_relat_1(esk2_0),k2_relat_1(esk2_0)),k1_xboole_0)|~r1_tarski(k1_relat_1(esk2_0),esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_121])).
% 18.19/18.37  cnf(c_0_132, negated_conjecture, (k2_relat_1(esk2_0)=k1_xboole_0|v1_funct_2(esk2_0,k1_relat_1(esk2_0),k2_relat_1(esk2_0))|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0))))), inference(spm,[status(thm)],[c_0_122, c_0_69])).
% 18.19/18.37  cnf(c_0_133, negated_conjecture, (~v1_funct_2(X1,X2,X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(esk1_0,X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_20]), c_0_21])])).
% 18.19/18.37  cnf(c_0_134, negated_conjecture, (r1_tarski(esk2_0,k1_relat_1(k1_xboole_0))|~r1_tarski(esk1_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_28]), c_0_21])]), c_0_125])).
% 18.19/18.37  cnf(c_0_135, negated_conjecture, (r1_tarski(k2_relat_1(X1),esk1_0)|~r1_tarski(X1,k2_zfmisc_1(esk2_0,X2))|~r1_tarski(esk2_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_126])).
% 18.19/18.37  cnf(c_0_136, negated_conjecture, (r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk2_0)),esk2_0)|~r1_tarski(k1_relat_1(esk2_0),k1_xboole_0)|~r1_tarski(X1,k1_relat_1(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_86]), c_0_80])).
% 18.19/18.37  cnf(c_0_137, negated_conjecture, (k2_relat_1(esk2_0)=esk2_0|X1=esk2_0|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_85])])).
% 18.19/18.37  cnf(c_0_138, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_80, c_0_129])).
% 18.19/18.37  cnf(c_0_139, negated_conjecture, (~v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(esk1_0,X1)|~r1_tarski(X2,esk1_0)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_20]), c_0_21])])).
% 18.19/18.37  cnf(c_0_140, negated_conjecture, (v1_funct_2(esk2_0,k1_relat_1(esk2_0),k2_relat_1(esk2_0))|~v1_funct_2(esk2_0,k1_xboole_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0))))|~r1_tarski(k1_relat_1(esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_19]), c_0_21])])).
% 18.19/18.37  cnf(c_0_141, negated_conjecture, (~v1_funct_2(k1_xboole_0,esk2_0,k1_xboole_0)|~r1_tarski(esk1_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_134]), c_0_21])])).
% 18.19/18.37  cnf(c_0_142, negated_conjecture, (r1_tarski(k2_relat_1(X1),esk1_0)|~r1_tarski(X1,k2_zfmisc_1(esk2_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_135, c_0_81])])).
% 18.19/18.37  cnf(c_0_143, negated_conjecture, (r1_tarski(k2_zfmisc_1(X1,k2_relat_1(esk2_0)),esk2_0)|~r1_tarski(X1,k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_136, c_0_110])])).
% 18.19/18.37  cnf(c_0_144, negated_conjecture, (k2_relat_1(esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_137]), c_0_138])])).
% 18.19/18.37  cnf(c_0_145, negated_conjecture, (~v1_funct_2(esk2_0,k1_xboole_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0))))|~r1_tarski(esk1_0,esk2_0)|~r1_tarski(esk2_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_140]), c_0_36])]), c_0_99])).
% 18.19/18.37  cnf(c_0_146, negated_conjecture, (r1_tarski(esk2_0,X1)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_141, c_0_83])).
% 18.19/18.37  cnf(c_0_147, negated_conjecture, (r1_tarski(k2_relat_1(k1_relat_1(esk2_0)),esk1_0)), inference(spm,[status(thm)],[c_0_142, c_0_110])).
% 18.19/18.37  cnf(c_0_148, negated_conjecture, (r1_tarski(k2_zfmisc_1(X1,esk2_0),esk2_0)|~r1_tarski(X1,k1_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_143, c_0_144])).
% 18.19/18.37  cnf(c_0_149, negated_conjecture, (~v1_funct_2(esk2_0,k1_xboole_0,esk1_0)|~r1_tarski(esk1_0,esk2_0)|~r1_tarski(esk2_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_41]), c_0_34])])).
% 18.19/18.37  cnf(c_0_150, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(esk1_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_41]), c_0_21])])).
% 18.19/18.37  cnf(c_0_151, plain, (r1_tarski(k2_zfmisc_1(X1,X2),X3)|~r1_tarski(X3,k1_xboole_0)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_30, c_0_86])).
% 18.19/18.37  cnf(c_0_152, negated_conjecture, (r1_tarski(k2_relat_1(k1_relat_1(esk2_0)),k1_xboole_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(spm,[status(thm)],[c_0_147, c_0_73])).
% 18.19/18.37  cnf(c_0_153, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X2,X1),X3)|~r1_tarski(X3,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_20]), c_0_80])).
% 18.19/18.37  cnf(c_0_154, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk2_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_148, c_0_85])).
% 18.19/18.37  cnf(c_0_155, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_28]), c_0_85])])).
% 18.19/18.37  cnf(c_0_156, negated_conjecture, (~v1_funct_2(esk2_0,k1_xboole_0,k1_xboole_0)|~r1_tarski(esk1_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_28]), c_0_21])]), c_0_150])).
% 18.19/18.37  cnf(c_0_157, plain, (X1=X2|~r1_tarski(k2_zfmisc_1(X2,X2),k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_37])).
% 18.19/18.37  cnf(c_0_158, negated_conjecture, (r1_tarski(k2_zfmisc_1(X1,X2),esk1_0)|~r1_tarski(k2_relat_1(esk2_0),k1_xboole_0)|~r1_tarski(X1,k2_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_48, c_0_151])).
% 18.19/18.37  cnf(c_0_159, negated_conjecture, (r1_tarski(k2_relat_1(k1_relat_1(esk2_0)),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_41]), c_0_85])])).
% 18.19/18.37  cnf(c_0_160, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_154]), c_0_85])])).
% 18.19/18.37  cnf(c_0_161, negated_conjecture, (r1_tarski(k1_relat_1(k1_xboole_0),X1)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_155, c_0_83])).
% 18.19/18.37  cnf(c_0_162, negated_conjecture, (~v1_funct_2(X1,k1_xboole_0,k1_xboole_0)|~r1_tarski(k2_zfmisc_1(X1,X1),k1_xboole_0)|~r1_tarski(esk1_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_157]), c_0_150])).
% 18.19/18.37  cnf(c_0_163, negated_conjecture, (r1_tarski(k2_zfmisc_1(X1,X2),esk1_0)|~r1_tarski(X1,k2_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_158, c_0_129])])).
% 18.19/18.37  cnf(c_0_164, negated_conjecture, (r1_tarski(k2_relat_1(k1_relat_1(esk2_0)),X1)), inference(spm,[status(thm)],[c_0_80, c_0_159])).
% 18.19/18.37  cnf(c_0_165, negated_conjecture, (esk1_0=k1_xboole_0|k1_relset_1(k1_relat_1(k1_xboole_0),esk1_0,k1_xboole_0)!=k1_relat_1(k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_160]), c_0_160]), c_0_160])).
% 18.19/18.37  cnf(c_0_166, negated_conjecture, (r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161, c_0_41]), c_0_21])])).
% 18.19/18.37  cnf(c_0_167, negated_conjecture, (~v1_funct_2(X1,X2,X2)|~r1_tarski(k2_zfmisc_1(X1,X1),X2)|~r1_tarski(esk1_0,X2)|~r1_tarski(X2,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_20]), c_0_21])])).
% 18.19/18.37  cnf(c_0_168, negated_conjecture, (r1_tarski(k2_zfmisc_1(k2_relat_1(k1_relat_1(esk2_0)),X1),esk1_0)), inference(spm,[status(thm)],[c_0_163, c_0_164])).
% 18.19/18.37  cnf(c_0_169, negated_conjecture, (esk1_0=k1_xboole_0|k1_relset_1(k1_xboole_0,esk1_0,k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_28]), c_0_166])])).
% 18.19/18.37  cnf(c_0_170, negated_conjecture, (~v1_funct_2(k2_relat_1(k1_relat_1(esk2_0)),esk1_0,esk1_0)|~r1_tarski(esk1_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167, c_0_168]), c_0_53])])).
% 18.19/18.37  cnf(c_0_171, negated_conjecture, (esk1_0=k1_xboole_0|k1_relat_1(k1_xboole_0)!=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169, c_0_69]), c_0_19])).
% 18.19/18.37  cnf(c_0_172, negated_conjecture, (~v1_funct_2(k2_relat_1(k1_relat_1(esk2_0)),k1_xboole_0,k1_xboole_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_170, c_0_73]), c_0_21])])).
% 18.19/18.37  cnf(c_0_173, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 18.19/18.37  cnf(c_0_174, negated_conjecture, (r1_tarski(k2_zfmisc_1(k1_relat_1(k1_xboole_0),X1),esk1_0)), inference(spm,[status(thm)],[c_0_163, c_0_166])).
% 18.19/18.37  cnf(c_0_175, negated_conjecture, (esk1_0=k1_xboole_0|k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_41]), c_0_21])])).
% 18.19/18.37  cnf(c_0_176, negated_conjecture, (~v1_funct_2(k2_relat_1(k1_relat_1(esk2_0)),k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_172, c_0_41]), c_0_85])])).
% 18.19/18.37  cnf(c_0_177, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_173]), c_0_19])).
% 18.19/18.37  cnf(c_0_178, negated_conjecture, (k1_relat_1(k1_xboole_0)=esk1_0|X1=esk1_0|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_127, c_0_174])).
% 18.19/18.37  cnf(c_0_179, negated_conjecture, (esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_175, c_0_28]), c_0_166])])).
% 18.19/18.37  cnf(c_0_180, negated_conjecture, (~v1_funct_2(k2_relat_1(k1_relat_1(k1_xboole_0)),k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176, c_0_28]), c_0_85])])).
% 18.19/18.37  cnf(c_0_181, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_177, c_0_41])).
% 18.19/18.37  cnf(c_0_182, negated_conjecture, (k1_relat_1(k1_xboole_0)=k1_xboole_0|X1=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_178, c_0_179]), c_0_179]), c_0_179]), c_0_21])])).
% 18.19/18.37  cnf(c_0_183, negated_conjecture, (~v1_funct_2(k2_relat_1(k1_relat_1(X1)),X1,X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180, c_0_20]), c_0_21])])).
% 18.19/18.37  cnf(c_0_184, plain, (v1_funct_2(X1,k1_xboole_0,X2)|~r1_tarski(k1_relset_1(k1_xboole_0,X2,X1),k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_181, c_0_28])).
% 18.19/18.37  cnf(c_0_185, negated_conjecture, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(ef,[status(thm)],[c_0_182])).
% 18.19/18.37  cnf(c_0_186, negated_conjecture, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_28]), c_0_85])])).
% 18.19/18.37  cnf(c_0_187, negated_conjecture, (r1_tarski(k2_relat_1(k1_relat_1(k1_xboole_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_28]), c_0_85])])).
% 18.19/18.37  cnf(c_0_188, negated_conjecture, (~r1_tarski(k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_183, c_0_184]), c_0_21]), c_0_185]), c_0_186]), c_0_187])])).
% 18.19/18.37  cnf(c_0_189, negated_conjecture, (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_188, c_0_69]), c_0_166]), c_0_19])])).
% 18.19/18.37  cnf(c_0_190, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_189, c_0_41]), c_0_21])]), ['proof']).
% 18.19/18.37  # SZS output end CNFRefutation
% 18.19/18.37  # Proof object total steps             : 191
% 18.19/18.37  # Proof object clause steps            : 170
% 18.19/18.37  # Proof object formula steps           : 21
% 18.19/18.37  # Proof object conjectures             : 129
% 18.19/18.37  # Proof object clause conjectures      : 126
% 18.19/18.37  # Proof object formula conjectures     : 3
% 18.19/18.37  # Proof object initial clauses used    : 19
% 18.19/18.37  # Proof object initial formulas used   : 10
% 18.19/18.37  # Proof object generating inferences   : 138
% 18.19/18.37  # Proof object simplifying inferences  : 196
% 18.19/18.37  # Training examples: 0 positive, 0 negative
% 18.19/18.37  # Parsed axioms                        : 10
% 18.19/18.37  # Removed by relevancy pruning/SinE    : 0
% 18.19/18.37  # Initial clauses                      : 24
% 18.19/18.37  # Removed in clause preprocessing      : 0
% 18.19/18.37  # Initial clauses in saturation        : 24
% 18.19/18.37  # Processed clauses                    : 83334
% 18.19/18.37  # ...of these trivial                  : 161
% 18.19/18.37  # ...subsumed                          : 75794
% 18.19/18.37  # ...remaining for further processing  : 7379
% 18.19/18.37  # Other redundant clauses eliminated   : 1144
% 18.19/18.37  # Clauses deleted for lack of memory   : 0
% 18.19/18.37  # Backward-subsumed                    : 2267
% 18.19/18.37  # Backward-rewritten                   : 3619
% 18.19/18.37  # Generated clauses                    : 2540793
% 18.19/18.37  # ...of the previous two non-trivial   : 2452161
% 18.19/18.37  # Contextual simplify-reflections      : 782
% 18.19/18.37  # Paramodulations                      : 2539397
% 18.19/18.37  # Factorizations                       : 253
% 18.19/18.37  # Equation resolutions                 : 1144
% 18.19/18.37  # Propositional unsat checks           : 0
% 18.19/18.37  #    Propositional check models        : 0
% 18.19/18.37  #    Propositional check unsatisfiable : 0
% 18.19/18.37  #    Propositional clauses             : 0
% 18.19/18.37  #    Propositional clauses after purity: 0
% 18.19/18.37  #    Propositional unsat core size     : 0
% 18.19/18.37  #    Propositional preprocessing time  : 0.000
% 18.19/18.37  #    Propositional encoding time       : 0.000
% 18.19/18.37  #    Propositional solver time         : 0.000
% 18.19/18.37  #    Success case prop preproc time    : 0.000
% 18.19/18.37  #    Success case prop encoding time   : 0.000
% 18.19/18.37  #    Success case prop solver time     : 0.000
% 18.19/18.37  # Current number of processed clauses  : 1462
% 18.19/18.37  #    Positive orientable unit clauses  : 10
% 18.19/18.37  #    Positive unorientable unit clauses: 0
% 18.19/18.37  #    Negative unit clauses             : 3
% 18.19/18.37  #    Non-unit-clauses                  : 1449
% 18.19/18.37  # Current number of unprocessed clauses: 1893889
% 18.19/18.37  # ...number of literals in the above   : 10945296
% 18.19/18.37  # Current number of archived formulas  : 0
% 18.19/18.37  # Current number of archived clauses   : 5909
% 18.19/18.37  # Clause-clause subsumption calls (NU) : 9216538
% 18.19/18.37  # Rec. Clause-clause subsumption calls : 1067091
% 18.19/18.37  # Non-unit clause-clause subsumptions  : 72520
% 18.19/18.37  # Unit Clause-clause subsumption calls : 107958
% 18.19/18.37  # Rewrite failures with RHS unbound    : 0
% 18.19/18.37  # BW rewrite match attempts            : 799
% 18.19/18.37  # BW rewrite match successes           : 132
% 18.19/18.37  # Condensation attempts                : 0
% 18.19/18.37  # Condensation successes               : 0
% 18.19/18.37  # Termbank termtop insertions          : 45460896
% 18.25/18.45  
% 18.25/18.45  # -------------------------------------------------
% 18.25/18.45  # User time                : 17.290 s
% 18.25/18.45  # System time              : 0.816 s
% 18.25/18.45  # Total time               : 18.107 s
% 18.25/18.45  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
