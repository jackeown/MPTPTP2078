%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:01 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 421 expanded)
%              Number of clauses        :   84 ( 193 expanded)
%              Number of leaves         :   19 ( 106 expanded)
%              Depth                    :   19
%              Number of atoms          :  317 (1262 expanded)
%              Number of equality atoms :  106 ( 309 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t4_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X2)
     => v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc10_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

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

fof(c_0_19,plain,(
    ! [X19,X20,X21] :
      ( ~ r2_hidden(X19,X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X21))
      | ~ v1_xboole_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_20,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X17,k1_zfmisc_1(X18))
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | m1_subset_1(X17,k1_zfmisc_1(X18)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r1_tarski(k2_relat_1(X2),X1)
         => ( v1_funct_1(X2)
            & v1_funct_2(X2,k1_relat_1(X2),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t4_funct_2])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & r1_tarski(k2_relat_1(esk4_0),esk3_0)
    & ( ~ v1_funct_1(esk4_0)
      | ~ v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0)
      | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_25,plain,(
    ! [X24] :
      ( ~ v1_relat_1(X24)
      | r1_tarski(X24,k2_zfmisc_1(k1_relat_1(X24),k2_relat_1(X24))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

fof(c_0_26,plain,(
    ! [X15,X16] :
      ( ( k2_zfmisc_1(X15,X16) != k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0 )
      & ( X15 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_27,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X5] :
      ( X5 = k1_xboole_0
      | r2_hidden(esk1_1(X5),X5) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_30,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | r1_tarski(X9,k2_xboole_0(X11,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_31,plain,(
    ! [X12] : k2_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk4_0))
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X33] : m1_subset_1(k6_relat_1(X33),k1_zfmisc_1(k2_zfmisc_1(X33,X33))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

fof(c_0_37,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | X4 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_38,plain,(
    ! [X13,X14] :
      ( ~ v1_xboole_0(X14)
      | v1_xboole_0(k2_zfmisc_1(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,k1_xboole_0)
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( k2_relat_1(esk4_0) = k1_xboole_0
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_45,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( v1_xboole_0(k2_zfmisc_1(X2,X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_48,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk4_0,k1_xboole_0)
    | ~ v1_xboole_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_51,plain,
    ( r1_tarski(k6_relat_1(X1),k2_zfmisc_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( r1_tarski(k6_relat_1(X1),k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

fof(c_0_56,plain,(
    ! [X30,X31,X32] :
      ( ~ v1_relat_1(X32)
      | ~ r1_tarski(k1_relat_1(X32),X30)
      | ~ r1_tarski(k2_relat_1(X32),X31)
      | m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

fof(c_0_57,plain,(
    ! [X26] :
      ( k1_relat_1(k6_relat_1(X26)) = X26
      & k2_relat_1(k6_relat_1(X26)) = X26 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_58,negated_conjecture,
    ( X1 = esk4_0
    | ~ r1_tarski(X1,esk4_0)
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( r1_tarski(k6_relat_1(X1),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_55])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_61,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( k6_relat_1(X1) = esk4_0
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

fof(c_0_63,plain,(
    ! [X23] :
      ( ~ v1_xboole_0(X23)
      | v1_xboole_0(k1_relat_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_relat_1])])).

cnf(c_0_64,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_44,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( k1_relat_1(esk4_0) = X1
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,plain,
    ( v1_xboole_0(k1_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( k2_relat_1(esk4_0) = X1
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(X1,esk3_0))
    | ~ r1_tarski(k1_relat_1(esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_28]),c_0_43])])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_71,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_relat_1(X1)
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( k2_relat_1(esk4_0) = k1_relat_1(X1)
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_67])).

cnf(c_0_73,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_74,plain,(
    ! [X22] :
      ( ~ v1_xboole_0(X22)
      | v1_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_75,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | k1_relset_1(X27,X28,X29) = k1_relat_1(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(esk4_0,k1_xboole_0)
    | esk3_0 != k1_xboole_0
    | ~ r1_tarski(k1_relat_1(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_33])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( k2_relat_1(esk4_0) = k1_relat_1(esk4_0)
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_79,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,k1_xboole_0)
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_73])).

cnf(c_0_81,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_82,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_67])).

fof(c_0_83,plain,(
    ! [X34,X35,X36] :
      ( ( ~ v1_funct_2(X36,X34,X35)
        | X34 = k1_relset_1(X34,X35,X36)
        | X35 = k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X34 != k1_relset_1(X34,X35,X36)
        | v1_funct_2(X36,X34,X35)
        | X35 = k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( ~ v1_funct_2(X36,X34,X35)
        | X34 = k1_relset_1(X34,X35,X36)
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X34 != k1_relset_1(X34,X35,X36)
        | v1_funct_2(X36,X34,X35)
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( ~ v1_funct_2(X36,X34,X35)
        | X36 = k1_xboole_0
        | X34 = k1_xboole_0
        | X35 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X36 != k1_xboole_0
        | v1_funct_2(X36,X34,X35)
        | X34 = k1_xboole_0
        | X35 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_84,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_85,plain,
    ( k2_xboole_0(X1,X2) = X3
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_39])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(esk4_0,k1_xboole_0)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_87,negated_conjecture,
    ( ~ v1_funct_1(esk4_0)
    | ~ v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_88,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_89,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk3_0
    | ~ r1_tarski(esk3_0,k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_28])).

cnf(c_0_90,negated_conjecture,
    ( k2_relat_1(esk4_0) = k1_relat_1(esk4_0)
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_91,plain,
    ( r1_tarski(X1,k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])).

cnf(c_0_92,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_93,plain,
    ( k1_relset_1(X1,X1,k6_relat_1(X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_45]),c_0_61])).

cnf(c_0_94,plain,
    ( X1 = X2
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_85,c_0_40])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_86])).

cnf(c_0_96,plain,
    ( r1_tarski(k6_relat_1(X1),k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_33])).

cnf(c_0_97,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k1_xboole_0))
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_33])).

cnf(c_0_98,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88])])).

cnf(c_0_99,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk3_0
    | ~ r1_tarski(esk3_0,k1_relat_1(esk4_0))
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_100,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_91])).

cnf(c_0_101,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_102,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k6_relat_1(X1),X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_45]),c_0_93])])).

cnf(c_0_103,negated_conjecture,
    ( X1 = esk4_0
    | esk3_0 != k1_xboole_0
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_104,plain,
    ( r1_tarski(k6_relat_1(X1),X2)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_96])).

cnf(c_0_105,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_97]),c_0_79])])).

cnf(c_0_106,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_60]),c_0_43]),c_0_77]),c_0_28])])).

cnf(c_0_107,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk3_0
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_108,plain,
    ( v1_funct_2(k6_relat_1(X1),X1,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_45]),c_0_93])]),c_0_102])).

cnf(c_0_109,negated_conjecture,
    ( k6_relat_1(X1) = esk4_0
    | esk3_0 != k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_110,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_61])).

cnf(c_0_111,plain,
    ( k6_relat_1(X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_105,c_0_35])).

cnf(c_0_112,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,esk3_0,esk3_0)
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_113,negated_conjecture,
    ( v1_funct_2(esk4_0,X1,X1)
    | esk3_0 != k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_114,plain,
    ( v1_xboole_0(X1)
    | X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_79])])).

cnf(c_0_115,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relat_1(X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_23])).

cnf(c_0_116,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relset_1(X3,X1,X2) != X3
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_23])).

cnf(c_0_117,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_114])).

cnf(c_0_118,negated_conjecture,
    ( k1_relset_1(X1,esk3_0,esk4_0) = k1_relat_1(esk4_0)
    | ~ r1_tarski(k1_relat_1(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_115,c_0_69])).

cnf(c_0_119,negated_conjecture,
    ( v1_funct_2(esk4_0,X1,esk3_0)
    | k1_relset_1(X1,esk3_0,esk4_0) != X1
    | ~ r1_tarski(k1_relat_1(esk4_0),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_69]),c_0_117])).

cnf(c_0_120,negated_conjecture,
    ( k1_relset_1(k1_relat_1(esk4_0),esk3_0,esk4_0) = k1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_77])).

cnf(c_0_121,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_77]),c_0_120])]),c_0_106]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:28:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.48  # AutoSched0-Mode selected heuristic G_E___107_C36_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.21/0.48  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.48  #
% 0.21/0.48  # Preprocessing time       : 0.032 s
% 0.21/0.48  # Presaturation interreduction done
% 0.21/0.48  
% 0.21/0.48  # Proof found!
% 0.21/0.48  # SZS status Theorem
% 0.21/0.48  # SZS output start CNFRefutation
% 0.21/0.48  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.21/0.48  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.48  fof(t4_funct_2, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 0.21/0.48  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 0.21/0.48  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.21/0.48  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.21/0.48  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.21/0.48  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.21/0.48  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 0.21/0.48  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.21/0.48  fof(fc3_zfmisc_1, axiom, ![X1, X2]:(v1_xboole_0(X2)=>v1_xboole_0(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 0.21/0.48  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.48  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.21/0.48  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.21/0.48  fof(fc10_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_xboole_0(k1_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 0.21/0.48  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.21/0.48  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.21/0.48  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.21/0.48  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.21/0.48  fof(c_0_19, plain, ![X19, X20, X21]:(~r2_hidden(X19,X20)|~m1_subset_1(X20,k1_zfmisc_1(X21))|~v1_xboole_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.21/0.48  fof(c_0_20, plain, ![X17, X18]:((~m1_subset_1(X17,k1_zfmisc_1(X18))|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|m1_subset_1(X17,k1_zfmisc_1(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.48  fof(c_0_21, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))))))), inference(assume_negation,[status(cth)],[t4_funct_2])).
% 0.21/0.48  cnf(c_0_22, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.48  cnf(c_0_23, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.48  fof(c_0_24, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&(r1_tarski(k2_relat_1(esk4_0),esk3_0)&(~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.21/0.48  fof(c_0_25, plain, ![X24]:(~v1_relat_1(X24)|r1_tarski(X24,k2_zfmisc_1(k1_relat_1(X24),k2_relat_1(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.21/0.48  fof(c_0_26, plain, ![X15, X16]:((k2_zfmisc_1(X15,X16)!=k1_xboole_0|(X15=k1_xboole_0|X16=k1_xboole_0))&((X15!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0)&(X16!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.21/0.48  cnf(c_0_27, plain, (~r1_tarski(X1,X2)|~r2_hidden(X3,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.21/0.48  cnf(c_0_28, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.48  fof(c_0_29, plain, ![X5]:(X5=k1_xboole_0|r2_hidden(esk1_1(X5),X5)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.21/0.48  fof(c_0_30, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|r1_tarski(X9,k2_xboole_0(X11,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.21/0.48  fof(c_0_31, plain, ![X12]:k2_xboole_0(X12,k1_xboole_0)=X12, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.21/0.48  cnf(c_0_32, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.48  cnf(c_0_33, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.48  cnf(c_0_34, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk4_0))|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.48  cnf(c_0_35, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.48  fof(c_0_36, plain, ![X33]:m1_subset_1(k6_relat_1(X33),k1_zfmisc_1(k2_zfmisc_1(X33,X33))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.21/0.48  fof(c_0_37, plain, ![X4]:(~v1_xboole_0(X4)|X4=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.21/0.48  fof(c_0_38, plain, ![X13, X14]:(~v1_xboole_0(X14)|v1_xboole_0(k2_zfmisc_1(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).
% 0.21/0.48  cnf(c_0_39, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.48  cnf(c_0_40, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.48  cnf(c_0_41, plain, (r1_tarski(X1,k1_xboole_0)|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.48  cnf(c_0_42, negated_conjecture, (k2_relat_1(esk4_0)=k1_xboole_0|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.21/0.48  cnf(c_0_43, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.48  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.48  cnf(c_0_45, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.48  cnf(c_0_46, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.48  cnf(c_0_47, plain, (v1_xboole_0(k2_zfmisc_1(X2,X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.48  fof(c_0_48, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.48  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.48  cnf(c_0_50, negated_conjecture, (r1_tarski(esk4_0,k1_xboole_0)|~v1_xboole_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])])).
% 0.21/0.48  cnf(c_0_51, plain, (r1_tarski(k6_relat_1(X1),k2_zfmisc_1(X1,X1))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.21/0.48  cnf(c_0_52, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.21/0.48  cnf(c_0_53, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.48  cnf(c_0_54, negated_conjecture, (r1_tarski(esk4_0,X1)|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.21/0.48  cnf(c_0_55, plain, (r1_tarski(k6_relat_1(X1),k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.48  fof(c_0_56, plain, ![X30, X31, X32]:(~v1_relat_1(X32)|(~r1_tarski(k1_relat_1(X32),X30)|~r1_tarski(k2_relat_1(X32),X31)|m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.21/0.48  fof(c_0_57, plain, ![X26]:(k1_relat_1(k6_relat_1(X26))=X26&k2_relat_1(k6_relat_1(X26))=X26), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.21/0.48  cnf(c_0_58, negated_conjecture, (X1=esk4_0|~r1_tarski(X1,esk4_0)|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.21/0.48  cnf(c_0_59, plain, (r1_tarski(k6_relat_1(X1),X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_49, c_0_55])).
% 0.21/0.48  cnf(c_0_60, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.21/0.48  cnf(c_0_61, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.21/0.48  cnf(c_0_62, negated_conjecture, (k6_relat_1(X1)=esk4_0|~v1_xboole_0(esk3_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.21/0.48  fof(c_0_63, plain, ![X23]:(~v1_xboole_0(X23)|v1_xboole_0(k1_relat_1(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_relat_1])])).
% 0.21/0.48  cnf(c_0_64, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.21/0.48  cnf(c_0_65, plain, (r1_tarski(X1,k2_zfmisc_1(X2,X3))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_44, c_0_60])).
% 0.21/0.48  cnf(c_0_66, negated_conjecture, (k1_relat_1(esk4_0)=X1|~v1_xboole_0(esk3_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.21/0.48  cnf(c_0_67, plain, (v1_xboole_0(k1_relat_1(X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.21/0.48  cnf(c_0_68, negated_conjecture, (k2_relat_1(esk4_0)=X1|~v1_xboole_0(esk3_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_64, c_0_62])).
% 0.21/0.48  cnf(c_0_69, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(X1,esk3_0))|~r1_tarski(k1_relat_1(esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_28]), c_0_43])])).
% 0.21/0.48  cnf(c_0_70, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.48  cnf(c_0_71, negated_conjecture, (k1_relat_1(esk4_0)=k1_relat_1(X1)|~v1_xboole_0(esk3_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.21/0.48  cnf(c_0_72, negated_conjecture, (k2_relat_1(esk4_0)=k1_relat_1(X1)|~v1_xboole_0(esk3_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_68, c_0_67])).
% 0.21/0.48  cnf(c_0_73, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.48  fof(c_0_74, plain, ![X22]:(~v1_xboole_0(X22)|v1_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.21/0.48  fof(c_0_75, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|k1_relset_1(X27,X28,X29)=k1_relat_1(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.21/0.48  cnf(c_0_76, negated_conjecture, (r1_tarski(esk4_0,k1_xboole_0)|esk3_0!=k1_xboole_0|~r1_tarski(k1_relat_1(esk4_0),X1)), inference(spm,[status(thm)],[c_0_69, c_0_33])).
% 0.21/0.48  cnf(c_0_77, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_70])).
% 0.21/0.48  cnf(c_0_78, negated_conjecture, (k2_relat_1(esk4_0)=k1_relat_1(esk4_0)|~v1_xboole_0(esk3_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.21/0.48  cnf(c_0_79, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.21/0.48  cnf(c_0_80, plain, (r1_tarski(X1,k1_xboole_0)|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_73])).
% 0.21/0.48  cnf(c_0_81, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.21/0.48  cnf(c_0_82, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_46, c_0_67])).
% 0.21/0.48  fof(c_0_83, plain, ![X34, X35, X36]:((((~v1_funct_2(X36,X34,X35)|X34=k1_relset_1(X34,X35,X36)|X35=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(X34!=k1_relset_1(X34,X35,X36)|v1_funct_2(X36,X34,X35)|X35=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))&((~v1_funct_2(X36,X34,X35)|X34=k1_relset_1(X34,X35,X36)|X34!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(X34!=k1_relset_1(X34,X35,X36)|v1_funct_2(X36,X34,X35)|X34!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))))&((~v1_funct_2(X36,X34,X35)|X36=k1_xboole_0|X34=k1_xboole_0|X35!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(X36!=k1_xboole_0|v1_funct_2(X36,X34,X35)|X34=k1_xboole_0|X35!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.21/0.48  cnf(c_0_84, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.21/0.48  cnf(c_0_85, plain, (k2_xboole_0(X1,X2)=X3|~r1_tarski(k2_xboole_0(X1,X2),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_53, c_0_39])).
% 0.21/0.48  cnf(c_0_86, negated_conjecture, (r1_tarski(esk4_0,k1_xboole_0)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.21/0.48  cnf(c_0_87, negated_conjecture, (~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.48  cnf(c_0_88, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.48  cnf(c_0_89, negated_conjecture, (k2_relat_1(esk4_0)=esk3_0|~r1_tarski(esk3_0,k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_53, c_0_28])).
% 0.21/0.48  cnf(c_0_90, negated_conjecture, (k2_relat_1(esk4_0)=k1_relat_1(esk4_0)|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.21/0.48  cnf(c_0_91, plain, (r1_tarski(X1,k1_xboole_0)|~v1_xboole_0(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])).
% 0.21/0.48  cnf(c_0_92, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.21/0.48  cnf(c_0_93, plain, (k1_relset_1(X1,X1,k6_relat_1(X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_45]), c_0_61])).
% 0.21/0.48  cnf(c_0_94, plain, (X1=X2|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_85, c_0_40])).
% 0.21/0.48  cnf(c_0_95, negated_conjecture, (r1_tarski(esk4_0,X1)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_86])).
% 0.21/0.48  cnf(c_0_96, plain, (r1_tarski(k6_relat_1(X1),k1_xboole_0)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_33])).
% 0.21/0.48  cnf(c_0_97, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k1_xboole_0))|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_33])).
% 0.21/0.48  cnf(c_0_98, negated_conjecture, (~v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_88])])).
% 0.21/0.48  cnf(c_0_99, negated_conjecture, (k1_relat_1(esk4_0)=esk3_0|~r1_tarski(esk3_0,k1_relat_1(esk4_0))|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.21/0.48  cnf(c_0_100, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_49, c_0_91])).
% 0.21/0.48  cnf(c_0_101, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.21/0.48  cnf(c_0_102, plain, (X1=k1_xboole_0|v1_funct_2(k6_relat_1(X1),X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_45]), c_0_93])])).
% 0.21/0.48  cnf(c_0_103, negated_conjecture, (X1=esk4_0|esk3_0!=k1_xboole_0|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.21/0.48  cnf(c_0_104, plain, (r1_tarski(k6_relat_1(X1),X2)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_96])).
% 0.21/0.48  cnf(c_0_105, plain, (X1!=k1_xboole_0|~r2_hidden(X2,k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_97]), c_0_79])])).
% 0.21/0.48  cnf(c_0_106, negated_conjecture, (~v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_60]), c_0_43]), c_0_77]), c_0_28])])).
% 0.21/0.48  cnf(c_0_107, negated_conjecture, (k1_relat_1(esk4_0)=esk3_0|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.21/0.48  cnf(c_0_108, plain, (v1_funct_2(k6_relat_1(X1),X1,X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_45]), c_0_93])]), c_0_102])).
% 0.21/0.48  cnf(c_0_109, negated_conjecture, (k6_relat_1(X1)=esk4_0|esk3_0!=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.21/0.48  cnf(c_0_110, plain, (v1_xboole_0(X1)|~v1_xboole_0(k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_67, c_0_61])).
% 0.21/0.48  cnf(c_0_111, plain, (k6_relat_1(X1)=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_105, c_0_35])).
% 0.21/0.48  cnf(c_0_112, negated_conjecture, (~v1_funct_2(esk4_0,esk3_0,esk3_0)|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 0.21/0.48  cnf(c_0_113, negated_conjecture, (v1_funct_2(esk4_0,X1,X1)|esk3_0!=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 0.21/0.48  cnf(c_0_114, plain, (v1_xboole_0(X1)|X1!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_79])])).
% 0.21/0.48  cnf(c_0_115, plain, (k1_relset_1(X1,X2,X3)=k1_relat_1(X3)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_84, c_0_23])).
% 0.21/0.48  cnf(c_0_116, plain, (X1=k1_xboole_0|v1_funct_2(X2,X3,X1)|k1_relset_1(X3,X1,X2)!=X3|~r1_tarski(X2,k2_zfmisc_1(X3,X1))), inference(spm,[status(thm)],[c_0_92, c_0_23])).
% 0.21/0.48  cnf(c_0_117, negated_conjecture, (esk3_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_114])).
% 0.21/0.48  cnf(c_0_118, negated_conjecture, (k1_relset_1(X1,esk3_0,esk4_0)=k1_relat_1(esk4_0)|~r1_tarski(k1_relat_1(esk4_0),X1)), inference(spm,[status(thm)],[c_0_115, c_0_69])).
% 0.21/0.48  cnf(c_0_119, negated_conjecture, (v1_funct_2(esk4_0,X1,esk3_0)|k1_relset_1(X1,esk3_0,esk4_0)!=X1|~r1_tarski(k1_relat_1(esk4_0),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_69]), c_0_117])).
% 0.21/0.48  cnf(c_0_120, negated_conjecture, (k1_relset_1(k1_relat_1(esk4_0),esk3_0,esk4_0)=k1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_118, c_0_77])).
% 0.21/0.48  cnf(c_0_121, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_77]), c_0_120])]), c_0_106]), ['proof']).
% 0.21/0.48  # SZS output end CNFRefutation
% 0.21/0.48  # Proof object total steps             : 122
% 0.21/0.48  # Proof object clause steps            : 84
% 0.21/0.48  # Proof object formula steps           : 38
% 0.21/0.48  # Proof object conjectures             : 37
% 0.21/0.48  # Proof object clause conjectures      : 34
% 0.21/0.48  # Proof object formula conjectures     : 3
% 0.21/0.48  # Proof object initial clauses used    : 27
% 0.21/0.48  # Proof object initial formulas used   : 19
% 0.21/0.48  # Proof object generating inferences   : 55
% 0.21/0.48  # Proof object simplifying inferences  : 27
% 0.21/0.48  # Training examples: 0 positive, 0 negative
% 0.21/0.48  # Parsed axioms                        : 21
% 0.21/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.48  # Initial clauses                      : 41
% 0.21/0.48  # Removed in clause preprocessing      : 0
% 0.21/0.48  # Initial clauses in saturation        : 41
% 0.21/0.48  # Processed clauses                    : 1724
% 0.21/0.48  # ...of these trivial                  : 21
% 0.21/0.48  # ...subsumed                          : 1234
% 0.21/0.48  # ...remaining for further processing  : 469
% 0.21/0.48  # Other redundant clauses eliminated   : 2
% 0.21/0.48  # Clauses deleted for lack of memory   : 0
% 0.21/0.48  # Backward-subsumed                    : 60
% 0.21/0.48  # Backward-rewritten                   : 23
% 0.21/0.48  # Generated clauses                    : 4349
% 0.21/0.48  # ...of the previous two non-trivial   : 3913
% 0.21/0.48  # Contextual simplify-reflections      : 10
% 0.21/0.48  # Paramodulations                      : 4308
% 0.21/0.48  # Factorizations                       : 0
% 0.21/0.48  # Equation resolutions                 : 26
% 0.21/0.48  # Propositional unsat checks           : 0
% 0.21/0.48  #    Propositional check models        : 0
% 0.21/0.48  #    Propositional check unsatisfiable : 0
% 0.21/0.48  #    Propositional clauses             : 0
% 0.21/0.48  #    Propositional clauses after purity: 0
% 0.21/0.48  #    Propositional unsat core size     : 0
% 0.21/0.48  #    Propositional preprocessing time  : 0.000
% 0.21/0.48  #    Propositional encoding time       : 0.000
% 0.21/0.48  #    Propositional solver time         : 0.000
% 0.21/0.48  #    Success case prop preproc time    : 0.000
% 0.21/0.48  #    Success case prop encoding time   : 0.000
% 0.21/0.48  #    Success case prop solver time     : 0.000
% 0.21/0.48  # Current number of processed clauses  : 339
% 0.21/0.48  #    Positive orientable unit clauses  : 35
% 0.21/0.48  #    Positive unorientable unit clauses: 2
% 0.21/0.48  #    Negative unit clauses             : 14
% 0.21/0.48  #    Non-unit-clauses                  : 288
% 0.21/0.48  # Current number of unprocessed clauses: 2062
% 0.21/0.48  # ...number of literals in the above   : 9603
% 0.21/0.48  # Current number of archived formulas  : 0
% 0.21/0.48  # Current number of archived clauses   : 123
% 0.21/0.48  # Clause-clause subsumption calls (NU) : 11360
% 0.21/0.48  # Rec. Clause-clause subsumption calls : 7438
% 0.21/0.48  # Non-unit clause-clause subsumptions  : 588
% 0.21/0.48  # Unit Clause-clause subsumption calls : 1286
% 0.21/0.48  # Rewrite failures with RHS unbound    : 0
% 0.21/0.48  # BW rewrite match attempts            : 50
% 0.21/0.48  # BW rewrite match successes           : 15
% 0.21/0.48  # Condensation attempts                : 0
% 0.21/0.48  # Condensation successes               : 0
% 0.21/0.48  # Termbank termtop insertions          : 49080
% 0.21/0.48  
% 0.21/0.48  # -------------------------------------------------
% 0.21/0.48  # User time                : 0.118 s
% 0.21/0.48  # System time              : 0.009 s
% 0.21/0.48  # Total time               : 0.127 s
% 0.21/0.48  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
