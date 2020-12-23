%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:07 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 480 expanded)
%              Number of clauses        :   46 ( 230 expanded)
%              Number of leaves         :   12 ( 121 expanded)
%              Depth                    :   14
%              Number of atoms          :  150 (1059 expanded)
%              Number of equality atoms :   75 ( 569 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t60_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k1_xboole_0,X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
     => k8_relset_1(k1_xboole_0,X1,X3,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t1_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t150_relat_1,axiom,(
    ! [X1] : k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(t39_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
     => ( k7_relset_1(X2,X1,X3,k8_relset_1(X2,X1,X3,X1)) = k2_relset_1(X2,X1,X3)
        & k8_relset_1(X2,X1,X3,k7_relset_1(X2,X1,X3,X2)) = k1_relset_1(X2,X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

fof(t51_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => k8_relset_1(X1,X2,X3,k7_relset_1(X1,X2,X3,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_2)).

fof(c_0_12,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_xboole_0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
       => k8_relset_1(k1_xboole_0,X1,X3,X2) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t60_funct_2])).

fof(c_0_14,plain,(
    ! [X23,X24,X25,X26] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | k8_relset_1(X23,X24,X25,X26) = k10_relat_1(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_15,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))
    & k8_relset_1(k1_xboole_0,esk2_0,esk4_0,esk3_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_17,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X12,X13,X14] :
      ( ~ r2_hidden(X12,X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(X14))
      | ~ v1_xboole_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_22,plain,
    ( k8_relset_1(k1_xboole_0,X1,X2,X3) = k10_relat_1(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_25,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_26,plain,(
    ! [X33] :
      ( ( r2_hidden(esk1_1(X33),X33)
        | X33 = k1_xboole_0 )
      & ( r1_xboole_0(esk1_1(X33),X33)
        | X33 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_mcart_1])])])])).

cnf(c_0_27,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( k8_relset_1(k1_xboole_0,esk2_0,esk4_0,esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( k8_relset_1(k1_xboole_0,X1,X2,X3) = k8_relset_1(k1_xboole_0,X4,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k8_relset_1(X1,X2,k1_xboole_0,X3) = k10_relat_1(k1_xboole_0,X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_27])).

fof(c_0_33,plain,(
    ! [X27,X28,X29] :
      ( ( k7_relset_1(X27,X28,X29,X27) = k2_relset_1(X27,X28,X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( k8_relset_1(X27,X28,X29,X28) = k1_relset_1(X27,X28,X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

fof(c_0_34,plain,(
    ! [X19,X20,X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k7_relset_1(X19,X20,X21,X22) = k9_relat_1(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_35,plain,(
    ! [X15] : k9_relat_1(k1_xboole_0,X15) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t150_relat_1])).

cnf(c_0_36,negated_conjecture,
    ( k8_relset_1(k1_xboole_0,X1,esk4_0,esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_24])])).

cnf(c_0_37,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( k8_relset_1(X1,X2,k1_xboole_0,X3) = k8_relset_1(X4,X5,k1_xboole_0,X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_32])).

cnf(c_0_39,plain,
    ( k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_40,plain,(
    ! [X30,X31,X32] :
      ( ( k7_relset_1(X31,X30,X32,k8_relset_1(X31,X30,X32,X30)) = k2_relset_1(X31,X30,X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X30))) )
      & ( k8_relset_1(X31,X30,X32,k7_relset_1(X31,X30,X32,X31)) = k1_relset_1(X31,X30,X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_relset_1])])])).

cnf(c_0_41,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( k8_relset_1(k1_xboole_0,X1,k1_xboole_0,esk3_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k8_relset_1(X3,X4,k1_xboole_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_27])])).

cnf(c_0_45,plain,
    ( k8_relset_1(X1,X2,X3,k7_relset_1(X1,X2,X3,X1)) = k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,plain,
    ( k7_relset_1(X1,X2,k1_xboole_0,X3) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_27]),c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( k1_relset_1(X1,esk3_0,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k8_relset_1(X3,X4,k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_45]),c_0_46]),c_0_27])])).

cnf(c_0_49,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k8_relset_1(k1_xboole_0,X3,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_39]),c_0_18])])).

cnf(c_0_50,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_51,negated_conjecture,
    ( k8_relset_1(X1,X2,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,plain,
    ( k8_relset_1(X1,X2,k1_xboole_0,k1_xboole_0) = k8_relset_1(k1_xboole_0,X3,k1_xboole_0,X4) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_48]),c_0_27])])).

fof(c_0_53,plain,(
    ! [X37,X38,X39] :
      ( ( X38 = k1_xboole_0
        | k8_relset_1(X37,X38,X39,k7_relset_1(X37,X38,X39,X37)) = X37
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,X37,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X37 != k1_xboole_0
        | k8_relset_1(X37,X38,X39,k7_relset_1(X37,X38,X39,X37)) = X37
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,X37,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_funct_2])])])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_55,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( k8_relset_1(k1_xboole_0,X1,k1_xboole_0,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | k8_relset_1(X2,X1,X3,k7_relset_1(X2,X1,X3,X2)) = X2
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_37])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_60,plain,
    ( k8_relset_1(X1,k1_xboole_0,X2,X3) = k10_relat_1(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_18]),c_0_27])])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_37])).

cnf(c_0_63,plain,
    ( k8_relset_1(X1,k1_xboole_0,X2,X3) = k8_relset_1(X4,k1_xboole_0,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_60])).

cnf(c_0_64,plain,
    ( k8_relset_1(X1,X2,X3,k7_relset_1(X1,X2,X3,X1)) = X1
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( k8_relset_1(X1,k1_xboole_0,k1_xboole_0,X2) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_63]),c_0_27])])).

cnf(c_0_67,plain,
    ( k8_relset_1(k1_xboole_0,X1,X2,k7_relset_1(k1_xboole_0,X1,X2,k1_xboole_0)) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_64]),c_0_18])).

cnf(c_0_68,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_62,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_58]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:39:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_____0021_C18_F1_SE_CS_SP_S0Y
% 0.19/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.028 s
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.41  fof(t60_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_xboole_0,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))))=>k8_relset_1(k1_xboole_0,X1,X3,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 0.19/0.41  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.19/0.41  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.41  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.41  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.41  fof(t1_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&r1_xboole_0(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 0.19/0.41  fof(t38_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)&k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 0.19/0.41  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.19/0.41  fof(t150_relat_1, axiom, ![X1]:k9_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 0.19/0.41  fof(t39_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(k7_relset_1(X2,X1,X3,k8_relset_1(X2,X1,X3,X1))=k2_relset_1(X2,X1,X3)&k8_relset_1(X2,X1,X3,k7_relset_1(X2,X1,X3,X2))=k1_relset_1(X2,X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 0.19/0.41  fof(t51_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>k8_relset_1(X1,X2,X3,k7_relset_1(X1,X2,X3,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_funct_2)).
% 0.19/0.41  fof(c_0_12, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.41  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_xboole_0,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))))=>k8_relset_1(k1_xboole_0,X1,X3,X2)=k1_xboole_0)), inference(assume_negation,[status(cth)],[t60_funct_2])).
% 0.19/0.41  fof(c_0_14, plain, ![X23, X24, X25, X26]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|k8_relset_1(X23,X24,X25,X26)=k10_relat_1(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.19/0.41  cnf(c_0_15, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  fof(c_0_16, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,k1_xboole_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))))&k8_relset_1(k1_xboole_0,esk2_0,esk4_0,esk3_0)!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.19/0.41  cnf(c_0_17, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_18, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_15])).
% 0.19/0.41  fof(c_0_19, plain, ![X12, X13, X14]:(~r2_hidden(X12,X13)|~m1_subset_1(X13,k1_zfmisc_1(X14))|~v1_xboole_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.41  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  fof(c_0_21, plain, ![X8]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.41  cnf(c_0_22, plain, (k8_relset_1(k1_xboole_0,X1,X2,X3)=k10_relat_1(X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.41  cnf(c_0_23, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[c_0_20, c_0_18])).
% 0.19/0.41  cnf(c_0_25, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.41  fof(c_0_26, plain, ![X33]:((r2_hidden(esk1_1(X33),X33)|X33=k1_xboole_0)&(r1_xboole_0(esk1_1(X33),X33)|X33=k1_xboole_0)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_mcart_1])])])])).
% 0.19/0.41  cnf(c_0_27, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_28, negated_conjecture, (k8_relset_1(k1_xboole_0,esk2_0,esk4_0,esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_29, plain, (k8_relset_1(k1_xboole_0,X1,X2,X3)=k8_relset_1(k1_xboole_0,X4,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_22, c_0_22])).
% 0.19/0.41  cnf(c_0_30, negated_conjecture, (~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.19/0.41  cnf(c_0_31, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.41  cnf(c_0_32, plain, (k8_relset_1(X1,X2,k1_xboole_0,X3)=k10_relat_1(k1_xboole_0,X3)), inference(spm,[status(thm)],[c_0_17, c_0_27])).
% 0.19/0.41  fof(c_0_33, plain, ![X27, X28, X29]:((k7_relset_1(X27,X28,X29,X27)=k2_relset_1(X27,X28,X29)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(k8_relset_1(X27,X28,X29,X28)=k1_relset_1(X27,X28,X29)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).
% 0.19/0.41  fof(c_0_34, plain, ![X19, X20, X21, X22]:(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|k7_relset_1(X19,X20,X21,X22)=k9_relat_1(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.19/0.41  fof(c_0_35, plain, ![X15]:k9_relat_1(k1_xboole_0,X15)=k1_xboole_0, inference(variable_rename,[status(thm)],[t150_relat_1])).
% 0.19/0.41  cnf(c_0_36, negated_conjecture, (k8_relset_1(k1_xboole_0,X1,esk4_0,esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_24])])).
% 0.19/0.41  cnf(c_0_37, negated_conjecture, (esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.41  cnf(c_0_38, plain, (k8_relset_1(X1,X2,k1_xboole_0,X3)=k8_relset_1(X4,X5,k1_xboole_0,X3)), inference(spm,[status(thm)],[c_0_32, c_0_32])).
% 0.19/0.41  cnf(c_0_39, plain, (k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.41  fof(c_0_40, plain, ![X30, X31, X32]:((k7_relset_1(X31,X30,X32,k8_relset_1(X31,X30,X32,X30))=k2_relset_1(X31,X30,X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X30))))&(k8_relset_1(X31,X30,X32,k7_relset_1(X31,X30,X32,X31))=k1_relset_1(X31,X30,X32)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_relset_1])])])).
% 0.19/0.41  cnf(c_0_41, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.41  cnf(c_0_42, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.41  cnf(c_0_43, negated_conjecture, (k8_relset_1(k1_xboole_0,X1,k1_xboole_0,esk3_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.41  cnf(c_0_44, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k8_relset_1(X3,X4,k1_xboole_0,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_27])])).
% 0.19/0.41  cnf(c_0_45, plain, (k8_relset_1(X1,X2,X3,k7_relset_1(X1,X2,X3,X1))=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.41  cnf(c_0_46, plain, (k7_relset_1(X1,X2,k1_xboole_0,X3)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_27]), c_0_42])).
% 0.19/0.41  cnf(c_0_47, negated_conjecture, (k1_relset_1(X1,esk3_0,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.41  cnf(c_0_48, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k8_relset_1(X3,X4,k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_45]), c_0_46]), c_0_27])])).
% 0.19/0.41  cnf(c_0_49, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k8_relset_1(k1_xboole_0,X3,X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_39]), c_0_18])])).
% 0.19/0.41  cnf(c_0_50, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, (k8_relset_1(X1,X2,k1_xboole_0,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.41  cnf(c_0_52, plain, (k8_relset_1(X1,X2,k1_xboole_0,k1_xboole_0)=k8_relset_1(k1_xboole_0,X3,k1_xboole_0,X4)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_48]), c_0_27])])).
% 0.19/0.41  fof(c_0_53, plain, ![X37, X38, X39]:((X38=k1_xboole_0|k8_relset_1(X37,X38,X39,k7_relset_1(X37,X38,X39,X37))=X37|(~v1_funct_1(X39)|~v1_funct_2(X39,X37,X38)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))&(X37!=k1_xboole_0|k8_relset_1(X37,X38,X39,k7_relset_1(X37,X38,X39,X37))=X37|(~v1_funct_1(X39)|~v1_funct_2(X39,X37,X38)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_funct_2])])])).
% 0.19/0.41  cnf(c_0_54, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_55, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_50])).
% 0.19/0.41  cnf(c_0_56, negated_conjecture, (k8_relset_1(k1_xboole_0,X1,k1_xboole_0,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.41  cnf(c_0_57, plain, (X1=k1_xboole_0|k8_relset_1(X2,X1,X3,k7_relset_1(X2,X1,X3,X2))=X2|~v1_funct_1(X3)|~v1_funct_2(X3,X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.41  cnf(c_0_58, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_54, c_0_37])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_60, plain, (k8_relset_1(X1,k1_xboole_0,X2,X3)=k10_relat_1(X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_17, c_0_55])).
% 0.19/0.41  cnf(c_0_61, negated_conjecture, (X1=k1_xboole_0|~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_18]), c_0_27])])).
% 0.19/0.41  cnf(c_0_62, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,esk2_0)), inference(rw,[status(thm)],[c_0_59, c_0_37])).
% 0.19/0.41  cnf(c_0_63, plain, (k8_relset_1(X1,k1_xboole_0,X2,X3)=k8_relset_1(X4,k1_xboole_0,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_60, c_0_60])).
% 0.19/0.41  cnf(c_0_64, plain, (k8_relset_1(X1,X2,X3,k7_relset_1(X1,X2,X3,X1))=X1|X1!=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.41  cnf(c_0_65, negated_conjecture, (esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.41  cnf(c_0_66, negated_conjecture, (k8_relset_1(X1,k1_xboole_0,k1_xboole_0,X2)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_63]), c_0_27])])).
% 0.19/0.41  cnf(c_0_67, plain, (k8_relset_1(k1_xboole_0,X1,X2,k7_relset_1(k1_xboole_0,X1,X2,k1_xboole_0))=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_64]), c_0_18])).
% 0.19/0.41  cnf(c_0_68, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_62, c_0_65])).
% 0.19/0.41  cnf(c_0_69, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_58]), c_0_27])]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 70
% 0.19/0.41  # Proof object clause steps            : 46
% 0.19/0.41  # Proof object formula steps           : 24
% 0.19/0.41  # Proof object conjectures             : 22
% 0.19/0.41  # Proof object clause conjectures      : 19
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 17
% 0.19/0.41  # Proof object initial formulas used   : 12
% 0.19/0.41  # Proof object generating inferences   : 21
% 0.19/0.41  # Proof object simplifying inferences  : 33
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 17
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 29
% 0.19/0.41  # Removed in clause preprocessing      : 1
% 0.19/0.41  # Initial clauses in saturation        : 28
% 0.19/0.41  # Processed clauses                    : 2847
% 0.19/0.41  # ...of these trivial                  : 0
% 0.19/0.41  # ...subsumed                          : 2652
% 0.19/0.41  # ...remaining for further processing  : 195
% 0.19/0.41  # Other redundant clauses eliminated   : 7
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 87
% 0.19/0.41  # Backward-rewritten                   : 15
% 0.19/0.41  # Generated clauses                    : 3755
% 0.19/0.41  # ...of the previous two non-trivial   : 3600
% 0.19/0.41  # Contextual simplify-reflections      : 0
% 0.19/0.41  # Paramodulations                      : 3748
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 7
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 90
% 0.19/0.41  #    Positive orientable unit clauses  : 16
% 0.19/0.41  #    Positive unorientable unit clauses: 3
% 0.19/0.41  #    Negative unit clauses             : 13
% 0.19/0.41  #    Non-unit-clauses                  : 58
% 0.19/0.41  # Current number of unprocessed clauses: 8
% 0.19/0.41  # ...number of literals in the above   : 23
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 102
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 13881
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 12179
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 1429
% 0.19/0.41  # Unit Clause-clause subsumption calls : 207
% 0.19/0.41  # Rewrite failures with RHS unbound    : 1826
% 0.19/0.41  # BW rewrite match attempts            : 511
% 0.19/0.41  # BW rewrite match successes           : 238
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 36479
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.072 s
% 0.19/0.41  # System time              : 0.006 s
% 0.19/0.41  # Total time               : 0.078 s
% 0.19/0.41  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
