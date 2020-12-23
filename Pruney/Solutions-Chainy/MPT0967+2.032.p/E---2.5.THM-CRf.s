%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:25 EST 2020

% Result     : Theorem 1.02s
% Output     : CNFRefutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 756 expanded)
%              Number of clauses        :   84 ( 335 expanded)
%              Number of leaves         :   13 ( 189 expanded)
%              Depth                    :   18
%              Number of atoms          :  319 (2998 expanded)
%              Number of equality atoms :  122 ( 944 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X2,X3)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( r1_tarski(X2,X3)
         => ( ( X2 = k1_xboole_0
              & X1 != k1_xboole_0 )
            | ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_funct_2])).

fof(c_0_14,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X19,X20)
      | v1_xboole_0(X20)
      | r2_hidden(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_15,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk2_0,esk3_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & r1_tarski(esk3_0,esk4_0)
    & ( esk3_0 != k1_xboole_0
      | esk2_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(esk5_0)
      | ~ v1_funct_2(esk5_0,esk2_0,esk4_0)
      | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_16,plain,(
    ! [X18] : ~ v1_xboole_0(k1_zfmisc_1(X18)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_17,plain,(
    ! [X23,X24,X25] :
      ( ~ r2_hidden(X23,X24)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X25))
      | m1_subset_1(X23,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_18,plain,(
    ! [X21,X22] :
      ( ( ~ m1_subset_1(X21,k1_zfmisc_1(X22))
        | r1_tarski(X21,X22) )
      & ( ~ r1_tarski(X21,X22)
        | m1_subset_1(X21,k1_zfmisc_1(X22)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X11,X12] :
      ( ( k2_zfmisc_1(X11,X12) != k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk5_0,k1_zfmisc_1(k1_xboole_0))
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_29,plain,(
    ! [X16,X17] :
      ( ~ r1_tarski(X16,X17)
      | r1_tarski(k1_zfmisc_1(X16),k1_zfmisc_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

fof(c_0_30,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_31,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k1_relset_1(X26,X27,X28) = k1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_32,plain,(
    ! [X13,X14,X15] :
      ( ( r1_tarski(k2_zfmisc_1(X13,X15),k2_zfmisc_1(X14,X15))
        | ~ r1_tarski(X13,X14) )
      & ( r1_tarski(k2_zfmisc_1(X15,X13),k2_zfmisc_1(X15,X14))
        | ~ r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

fof(c_0_33,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_34,plain,(
    ! [X29,X30,X31] :
      ( ( ~ v1_funct_2(X31,X29,X30)
        | X29 = k1_relset_1(X29,X30,X31)
        | X30 = k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( X29 != k1_relset_1(X29,X30,X31)
        | v1_funct_2(X31,X29,X30)
        | X30 = k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( ~ v1_funct_2(X31,X29,X30)
        | X29 = k1_relset_1(X29,X30,X31)
        | X29 != k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( X29 != k1_relset_1(X29,X30,X31)
        | v1_funct_2(X31,X29,X30)
        | X29 != k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( ~ v1_funct_2(X31,X29,X30)
        | X31 = k1_xboole_0
        | X29 = k1_xboole_0
        | X30 != k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( X31 != k1_xboole_0
        | v1_funct_2(X31,X29,X30)
        | X29 = k1_xboole_0
        | X30 != k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk5_0,X1)
    | esk2_0 != k1_xboole_0
    | ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_39,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_41,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_funct_1(esk5_0)
    | ~ v1_funct_2(esk5_0,esk2_0,esk4_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_46,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(X1))
    | esk2_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_48,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_relset_1(esk2_0,esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_20])).

cnf(c_0_49,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_50,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_20])).

cnf(c_0_53,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)
    | X2 != k1_xboole_0
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_funct_2(esk5_0,esk2_0,esk4_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])])).

cnf(c_0_56,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_57,plain,
    ( k1_relset_1(X1,X2,X3) = X1
    | X1 != k1_xboole_0
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_26])).

cnf(c_0_58,negated_conjecture,
    ( k1_relset_1(X1,X2,esk5_0) = k1_relset_1(esk2_0,esk3_0,esk5_0)
    | esk2_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_47]),c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_60,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)
    | X3 != k1_xboole_0
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_49,c_0_42])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_62,plain,
    ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_49])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk2_0,esk3_0))
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_37])).

cnf(c_0_65,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_66,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_funct_2(esk5_0,esk2_0,esk4_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_26])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_26])).

cnf(c_0_68,negated_conjecture,
    ( v1_funct_2(esk5_0,X1,X2)
    | k1_relset_1(X1,X2,esk5_0) != X1
    | esk2_0 != k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_47])).

cnf(c_0_69,negated_conjecture,
    ( k1_relset_1(X1,X2,esk5_0) = esk2_0
    | esk2_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])]),c_0_47])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,esk3_0),k1_xboole_0)
    | esk4_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_71,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 = k1_xboole_0
    | X1 != k1_xboole_0
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_72,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,X1) = k2_zfmisc_1(esk2_0,esk3_0)
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,X1),esk5_0)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_73,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),X3)
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_funct_2(esk5_0,esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_2(esk5_0,X1,X2)
    | esk2_0 != k1_xboole_0
    | esk2_0 != X1
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk5_0,X1)
    | ~ r1_tarski(k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_25])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X4))
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_51,c_0_49])).

cnf(c_0_78,negated_conjecture,
    ( k2_zfmisc_1(X1,esk3_0) = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_70]),c_0_37])])).

cnf(c_0_79,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X1,X3)
    | X3 != k1_xboole_0
    | X2 != k1_xboole_0
    | ~ r1_tarski(X2,k2_zfmisc_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_24])).

cnf(c_0_80,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X3 != k1_xboole_0
    | ~ r1_tarski(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_42]),c_0_37])])).

cnf(c_0_81,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = esk5_0
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_52])).

cnf(c_0_82,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_83,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,X1) = k2_zfmisc_1(esk2_0,esk3_0)
    | X1 != k1_xboole_0
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_84,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(X1))
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_36])).

cnf(c_0_86,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X4,X3)
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_77,c_0_49])).

cnf(c_0_87,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | ~ v1_funct_2(esk5_0,esk2_0,esk4_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_42])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))
    | esk4_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_78])).

cnf(c_0_89,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k2_zfmisc_1(X1,X2),X1,X3)
    | X3 != k1_xboole_0
    | ~ r1_tarski(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_49]),c_0_80])).

cnf(c_0_90,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = esk5_0
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_81,c_0_73])).

cnf(c_0_91,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | X1 != k1_xboole_0
    | ~ r1_tarski(esk3_0,X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84]),c_0_42])).

cnf(c_0_92,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_85])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,esk4_0))
    | ~ r1_tarski(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_61])).

cnf(c_0_95,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | ~ v1_funct_2(esk5_0,esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_96,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,X1)
    | X1 != k1_xboole_0
    | ~ r1_tarski(esk3_0,X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_84]),c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( ~ v1_funct_2(esk5_0,esk2_0,esk4_0)
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_85])).

cnf(c_0_98,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relset_1(X3,X1,X2) != X3
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_24])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_54])])).

cnf(c_0_100,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_61])])).

cnf(c_0_101,negated_conjecture,
    ( ~ v1_funct_2(esk5_0,esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_49]),c_0_61])])).

cnf(c_0_102,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relat_1(X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_24])).

cnf(c_0_103,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_104,negated_conjecture,
    ( k1_relset_1(esk2_0,esk4_0,esk5_0) != esk2_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100]),c_0_101])).

cnf(c_0_105,negated_conjecture,
    ( k1_relset_1(X1,X2,esk5_0) = k1_relset_1(esk2_0,esk3_0,esk5_0)
    | ~ r1_tarski(esk5_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_102])).

cnf(c_0_106,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk5_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_20]),c_0_59])])).

cnf(c_0_107,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk5_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_99])])).

cnf(c_0_108,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_109,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_110,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_109])]),c_0_84]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:25:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.02/1.20  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 1.02/1.20  # and selection function PSelectComplexExceptUniqMaxHorn.
% 1.02/1.20  #
% 1.02/1.20  # Preprocessing time       : 0.029 s
% 1.02/1.20  
% 1.02/1.20  # Proof found!
% 1.02/1.20  # SZS status Theorem
% 1.02/1.20  # SZS output start CNFRefutation
% 1.02/1.20  fof(t9_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 1.02/1.20  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 1.02/1.20  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.02/1.20  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 1.02/1.20  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.02/1.20  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.02/1.20  fof(t79_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 1.02/1.20  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.02/1.20  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.02/1.20  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 1.02/1.20  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.02/1.20  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 1.02/1.20  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.02/1.20  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))))), inference(assume_negation,[status(cth)],[t9_funct_2])).
% 1.02/1.20  fof(c_0_14, plain, ![X19, X20]:(~m1_subset_1(X19,X20)|(v1_xboole_0(X20)|r2_hidden(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 1.02/1.20  fof(c_0_15, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk2_0,esk3_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(r1_tarski(esk3_0,esk4_0)&((esk3_0!=k1_xboole_0|esk2_0=k1_xboole_0)&(~v1_funct_1(esk5_0)|~v1_funct_2(esk5_0,esk2_0,esk4_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 1.02/1.20  fof(c_0_16, plain, ![X18]:~v1_xboole_0(k1_zfmisc_1(X18)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 1.02/1.20  fof(c_0_17, plain, ![X23, X24, X25]:(~r2_hidden(X23,X24)|~m1_subset_1(X24,k1_zfmisc_1(X25))|m1_subset_1(X23,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 1.02/1.20  fof(c_0_18, plain, ![X21, X22]:((~m1_subset_1(X21,k1_zfmisc_1(X22))|r1_tarski(X21,X22))&(~r1_tarski(X21,X22)|m1_subset_1(X21,k1_zfmisc_1(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.02/1.20  cnf(c_0_19, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.02/1.20  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.02/1.20  cnf(c_0_21, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.02/1.20  fof(c_0_22, plain, ![X11, X12]:((k2_zfmisc_1(X11,X12)!=k1_xboole_0|(X11=k1_xboole_0|X12=k1_xboole_0))&((X11!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0)&(X12!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 1.02/1.20  cnf(c_0_23, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.02/1.20  cnf(c_0_24, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.02/1.20  cnf(c_0_25, negated_conjecture, (r2_hidden(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 1.02/1.20  cnf(c_0_26, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.02/1.20  cnf(c_0_27, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 1.02/1.20  cnf(c_0_28, negated_conjecture, (r2_hidden(esk5_0,k1_zfmisc_1(k1_xboole_0))|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 1.02/1.20  fof(c_0_29, plain, ![X16, X17]:(~r1_tarski(X16,X17)|r1_tarski(k1_zfmisc_1(X16),k1_zfmisc_1(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).
% 1.02/1.20  fof(c_0_30, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 1.02/1.20  fof(c_0_31, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k1_relset_1(X26,X27,X28)=k1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 1.02/1.20  fof(c_0_32, plain, ![X13, X14, X15]:((r1_tarski(k2_zfmisc_1(X13,X15),k2_zfmisc_1(X14,X15))|~r1_tarski(X13,X14))&(r1_tarski(k2_zfmisc_1(X15,X13),k2_zfmisc_1(X15,X14))|~r1_tarski(X13,X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 1.02/1.20  fof(c_0_33, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.02/1.20  fof(c_0_34, plain, ![X29, X30, X31]:((((~v1_funct_2(X31,X29,X30)|X29=k1_relset_1(X29,X30,X31)|X30=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(X29!=k1_relset_1(X29,X30,X31)|v1_funct_2(X31,X29,X30)|X30=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))&((~v1_funct_2(X31,X29,X30)|X29=k1_relset_1(X29,X30,X31)|X29!=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(X29!=k1_relset_1(X29,X30,X31)|v1_funct_2(X31,X29,X30)|X29!=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))))&((~v1_funct_2(X31,X29,X30)|X31=k1_xboole_0|X29=k1_xboole_0|X30!=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(X31!=k1_xboole_0|v1_funct_2(X31,X29,X30)|X29=k1_xboole_0|X30!=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 1.02/1.20  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk5_0,X1)|esk2_0!=k1_xboole_0|~r1_tarski(k1_zfmisc_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 1.02/1.20  cnf(c_0_36, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.02/1.20  cnf(c_0_37, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.02/1.20  cnf(c_0_38, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.02/1.20  fof(c_0_39, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X8,X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 1.02/1.20  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.02/1.20  cnf(c_0_41, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.02/1.20  cnf(c_0_42, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.02/1.20  cnf(c_0_43, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.02/1.20  cnf(c_0_44, negated_conjecture, (~v1_funct_1(esk5_0)|~v1_funct_2(esk5_0,esk2_0,esk4_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.02/1.20  cnf(c_0_45, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.02/1.20  cnf(c_0_46, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.02/1.20  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(X1))|esk2_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 1.02/1.20  cnf(c_0_48, negated_conjecture, (k1_relat_1(esk5_0)=k1_relset_1(esk2_0,esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_38, c_0_20])).
% 1.02/1.20  cnf(c_0_49, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.02/1.20  cnf(c_0_50, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.02/1.20  cnf(c_0_51, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.02/1.20  cnf(c_0_52, negated_conjecture, (r1_tarski(esk5_0,k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_40, c_0_20])).
% 1.02/1.20  cnf(c_0_53, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)|X2!=k1_xboole_0|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.02/1.20  cnf(c_0_54, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_43])).
% 1.02/1.20  cnf(c_0_55, negated_conjecture, (~v1_funct_2(esk5_0,esk2_0,esk4_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45])])).
% 1.02/1.20  cnf(c_0_56, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.02/1.20  cnf(c_0_57, plain, (k1_relset_1(X1,X2,X3)=X1|X1!=k1_xboole_0|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_46, c_0_26])).
% 1.02/1.20  cnf(c_0_58, negated_conjecture, (k1_relset_1(X1,X2,esk5_0)=k1_relset_1(esk2_0,esk3_0,esk5_0)|esk2_0!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_47]), c_0_48])).
% 1.02/1.20  cnf(c_0_59, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.02/1.20  cnf(c_0_60, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)|X3!=k1_xboole_0|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_49, c_0_42])).
% 1.02/1.20  cnf(c_0_61, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.02/1.20  cnf(c_0_62, plain, (k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_50, c_0_49])).
% 1.02/1.20  cnf(c_0_63, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk2_0,esk3_0))|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 1.02/1.20  cnf(c_0_64, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_37])).
% 1.02/1.20  cnf(c_0_65, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 1.02/1.20  cnf(c_0_66, negated_conjecture, (esk2_0!=k1_xboole_0|~v1_funct_2(esk5_0,esk2_0,esk4_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_55, c_0_26])).
% 1.02/1.20  cnf(c_0_67, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_26])).
% 1.02/1.20  cnf(c_0_68, negated_conjecture, (v1_funct_2(esk5_0,X1,X2)|k1_relset_1(X1,X2,esk5_0)!=X1|esk2_0!=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_47])).
% 1.02/1.20  cnf(c_0_69, negated_conjecture, (k1_relset_1(X1,X2,esk5_0)=esk2_0|esk2_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])]), c_0_47])).
% 1.02/1.20  cnf(c_0_70, negated_conjecture, (r1_tarski(k2_zfmisc_1(X1,esk3_0),k1_xboole_0)|esk4_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 1.02/1.21  cnf(c_0_71, plain, (v1_funct_2(X1,X2,X3)|X2=k1_xboole_0|X1!=k1_xboole_0|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.02/1.21  cnf(c_0_72, negated_conjecture, (k2_zfmisc_1(esk2_0,X1)=k2_zfmisc_1(esk2_0,esk3_0)|~r1_tarski(k2_zfmisc_1(esk2_0,X1),esk5_0)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 1.02/1.21  cnf(c_0_73, plain, (r1_tarski(k2_zfmisc_1(X1,X2),X3)|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 1.02/1.21  cnf(c_0_74, negated_conjecture, (esk2_0!=k1_xboole_0|~v1_funct_2(esk5_0,esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 1.02/1.21  cnf(c_0_75, negated_conjecture, (v1_funct_2(esk5_0,X1,X2)|esk2_0!=k1_xboole_0|esk2_0!=X1|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 1.02/1.21  cnf(c_0_76, negated_conjecture, (m1_subset_1(esk5_0,X1)|~r1_tarski(k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)),X1)), inference(spm,[status(thm)],[c_0_27, c_0_25])).
% 1.02/1.21  cnf(c_0_77, plain, (r1_tarski(X1,k2_zfmisc_1(X2,X3))|~r1_tarski(X1,k2_zfmisc_1(X2,X4))|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_51, c_0_49])).
% 1.02/1.21  cnf(c_0_78, negated_conjecture, (k2_zfmisc_1(X1,esk3_0)=k1_xboole_0|esk4_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_70]), c_0_37])])).
% 1.02/1.21  cnf(c_0_79, plain, (X1=k1_xboole_0|v1_funct_2(X2,X1,X3)|X3!=k1_xboole_0|X2!=k1_xboole_0|~r1_tarski(X2,k2_zfmisc_1(X1,X3))), inference(spm,[status(thm)],[c_0_71, c_0_24])).
% 1.02/1.21  cnf(c_0_80, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X3!=k1_xboole_0|~r1_tarski(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_42]), c_0_37])])).
% 1.02/1.21  cnf(c_0_81, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=esk5_0|~r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),esk5_0)), inference(spm,[status(thm)],[c_0_50, c_0_52])).
% 1.02/1.21  cnf(c_0_82, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.02/1.21  cnf(c_0_83, negated_conjecture, (k2_zfmisc_1(esk2_0,X1)=k2_zfmisc_1(esk2_0,esk3_0)|X1!=k1_xboole_0|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 1.02/1.21  cnf(c_0_84, negated_conjecture, (esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 1.02/1.21  cnf(c_0_85, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(X1))|~r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_76, c_0_36])).
% 1.02/1.21  cnf(c_0_86, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X4,X3)|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_77, c_0_49])).
% 1.02/1.21  cnf(c_0_87, negated_conjecture, (esk4_0!=k1_xboole_0|~v1_funct_2(esk5_0,esk2_0,esk4_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_55, c_0_42])).
% 1.02/1.21  cnf(c_0_88, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))|esk4_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_78])).
% 1.02/1.21  cnf(c_0_89, plain, (X1=k1_xboole_0|v1_funct_2(k2_zfmisc_1(X1,X2),X1,X3)|X3!=k1_xboole_0|~r1_tarski(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_49]), c_0_80])).
% 1.02/1.21  cnf(c_0_90, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=esk5_0|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_81, c_0_73])).
% 1.02/1.21  cnf(c_0_91, negated_conjecture, (esk3_0=k1_xboole_0|X1!=k1_xboole_0|~r1_tarski(esk3_0,X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84]), c_0_42])).
% 1.02/1.21  cnf(c_0_92, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.02/1.21  cnf(c_0_93, negated_conjecture, (r1_tarski(esk5_0,X1)|~r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_40, c_0_85])).
% 1.02/1.21  cnf(c_0_94, negated_conjecture, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,esk4_0))|~r1_tarski(X2,esk3_0)), inference(spm,[status(thm)],[c_0_86, c_0_61])).
% 1.02/1.21  cnf(c_0_95, negated_conjecture, (esk4_0!=k1_xboole_0|~v1_funct_2(esk5_0,esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 1.02/1.21  cnf(c_0_96, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,X1)|X1!=k1_xboole_0|~r1_tarski(esk3_0,X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_84]), c_0_91])).
% 1.02/1.21  cnf(c_0_97, negated_conjecture, (~v1_funct_2(esk5_0,esk2_0,esk4_0)|~r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_55, c_0_85])).
% 1.02/1.21  cnf(c_0_98, plain, (X1=k1_xboole_0|v1_funct_2(X2,X3,X1)|k1_relset_1(X3,X1,X2)!=X3|~r1_tarski(X2,k2_zfmisc_1(X3,X1))), inference(spm,[status(thm)],[c_0_92, c_0_24])).
% 1.02/1.21  cnf(c_0_99, negated_conjecture, (r1_tarski(esk5_0,k2_zfmisc_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_54])])).
% 1.02/1.21  cnf(c_0_100, negated_conjecture, (esk4_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_61])])).
% 1.02/1.21  cnf(c_0_101, negated_conjecture, (~v1_funct_2(esk5_0,esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_49]), c_0_61])])).
% 1.02/1.21  cnf(c_0_102, plain, (k1_relset_1(X1,X2,X3)=k1_relat_1(X3)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_38, c_0_24])).
% 1.02/1.21  cnf(c_0_103, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.02/1.21  cnf(c_0_104, negated_conjecture, (k1_relset_1(esk2_0,esk4_0,esk5_0)!=esk2_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100]), c_0_101])).
% 1.02/1.21  cnf(c_0_105, negated_conjecture, (k1_relset_1(X1,X2,esk5_0)=k1_relset_1(esk2_0,esk3_0,esk5_0)|~r1_tarski(esk5_0,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_48, c_0_102])).
% 1.02/1.21  cnf(c_0_106, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk5_0)=esk2_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_20]), c_0_59])])).
% 1.02/1.21  cnf(c_0_107, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk5_0)!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_99])])).
% 1.02/1.21  cnf(c_0_108, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.02/1.21  cnf(c_0_109, negated_conjecture, (esk3_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_106, c_0_107])).
% 1.02/1.21  cnf(c_0_110, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_109])]), c_0_84]), ['proof']).
% 1.02/1.21  # SZS output end CNFRefutation
% 1.02/1.21  # Proof object total steps             : 111
% 1.02/1.21  # Proof object clause steps            : 84
% 1.02/1.21  # Proof object formula steps           : 27
% 1.02/1.21  # Proof object conjectures             : 50
% 1.02/1.21  # Proof object clause conjectures      : 47
% 1.02/1.21  # Proof object formula conjectures     : 3
% 1.02/1.21  # Proof object initial clauses used    : 27
% 1.02/1.21  # Proof object initial formulas used   : 13
% 1.02/1.21  # Proof object generating inferences   : 53
% 1.02/1.21  # Proof object simplifying inferences  : 35
% 1.02/1.21  # Training examples: 0 positive, 0 negative
% 1.02/1.21  # Parsed axioms                        : 14
% 1.02/1.21  # Removed by relevancy pruning/SinE    : 0
% 1.02/1.21  # Initial clauses                      : 35
% 1.02/1.21  # Removed in clause preprocessing      : 0
% 1.02/1.21  # Initial clauses in saturation        : 35
% 1.02/1.21  # Processed clauses                    : 7041
% 1.02/1.21  # ...of these trivial                  : 201
% 1.02/1.21  # ...subsumed                          : 5514
% 1.02/1.21  # ...remaining for further processing  : 1326
% 1.02/1.21  # Other redundant clauses eliminated   : 117
% 1.02/1.21  # Clauses deleted for lack of memory   : 0
% 1.02/1.21  # Backward-subsumed                    : 256
% 1.02/1.21  # Backward-rewritten                   : 636
% 1.02/1.21  # Generated clauses                    : 69919
% 1.02/1.21  # ...of the previous two non-trivial   : 62947
% 1.02/1.21  # Contextual simplify-reflections      : 142
% 1.02/1.21  # Paramodulations                      : 69738
% 1.02/1.21  # Factorizations                       : 57
% 1.02/1.21  # Equation resolutions                 : 123
% 1.02/1.21  # Propositional unsat checks           : 0
% 1.02/1.21  #    Propositional check models        : 0
% 1.02/1.21  #    Propositional check unsatisfiable : 0
% 1.02/1.21  #    Propositional clauses             : 0
% 1.02/1.21  #    Propositional clauses after purity: 0
% 1.02/1.21  #    Propositional unsat core size     : 0
% 1.02/1.21  #    Propositional preprocessing time  : 0.000
% 1.02/1.21  #    Propositional encoding time       : 0.000
% 1.02/1.21  #    Propositional solver time         : 0.000
% 1.02/1.21  #    Success case prop preproc time    : 0.000
% 1.02/1.21  #    Success case prop encoding time   : 0.000
% 1.02/1.21  #    Success case prop solver time     : 0.000
% 1.02/1.21  # Current number of processed clauses  : 431
% 1.02/1.21  #    Positive orientable unit clauses  : 19
% 1.02/1.21  #    Positive unorientable unit clauses: 1
% 1.02/1.21  #    Negative unit clauses             : 5
% 1.02/1.21  #    Non-unit-clauses                  : 406
% 1.02/1.21  # Current number of unprocessed clauses: 54396
% 1.02/1.21  # ...number of literals in the above   : 248044
% 1.02/1.21  # Current number of archived formulas  : 0
% 1.02/1.21  # Current number of archived clauses   : 893
% 1.02/1.21  # Clause-clause subsumption calls (NU) : 195955
% 1.02/1.21  # Rec. Clause-clause subsumption calls : 126848
% 1.02/1.21  # Non-unit clause-clause subsumptions  : 4221
% 1.02/1.21  # Unit Clause-clause subsumption calls : 1710
% 1.02/1.21  # Rewrite failures with RHS unbound    : 0
% 1.02/1.21  # BW rewrite match attempts            : 31
% 1.02/1.21  # BW rewrite match successes           : 16
% 1.02/1.21  # Condensation attempts                : 0
% 1.02/1.21  # Condensation successes               : 0
% 1.02/1.21  # Termbank termtop insertions          : 810376
% 1.02/1.21  
% 1.02/1.21  # -------------------------------------------------
% 1.02/1.21  # User time                : 0.838 s
% 1.02/1.21  # System time              : 0.033 s
% 1.02/1.21  # Total time               : 0.871 s
% 1.02/1.21  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
