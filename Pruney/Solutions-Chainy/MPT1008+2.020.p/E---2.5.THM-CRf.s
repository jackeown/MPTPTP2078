%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:32 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  101 (1699 expanded)
%              Number of clauses        :   63 ( 687 expanded)
%              Number of leaves         :   19 ( 472 expanded)
%              Depth                    :   19
%              Number of atoms          :  250 (3697 expanded)
%              Number of equality atoms :  105 (1998 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t62_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k1_tarski(X1),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => k2_relset_1(k1_tarski(X1),X2,X3) = k1_tarski(k1_funct_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t6_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

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

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(s3_funct_1__e15_31__wellord2,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = k1_tarski(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e15_31__wellord2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(t14_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => k2_relset_1(k1_tarski(X1),X2,X3) = k1_tarski(k1_funct_1(X3,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t62_funct_2])).

fof(c_0_20,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0)))
    & esk4_0 != k1_xboole_0
    & k2_relset_1(k1_tarski(esk3_0),esk4_0,esk5_0) != k1_tarski(k1_funct_1(esk5_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_21,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | k2_relset_1(X40,X41,X42) = k2_relat_1(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X11,X10)
        | X11 = X8
        | X11 = X9
        | X10 != k2_tarski(X8,X9) )
      & ( X12 != X8
        | r2_hidden(X12,X10)
        | X10 != k2_tarski(X8,X9) )
      & ( X12 != X9
        | r2_hidden(X12,X10)
        | X10 != k2_tarski(X8,X9) )
      & ( esk1_3(X13,X14,X15) != X13
        | ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k2_tarski(X13,X14) )
      & ( esk1_3(X13,X14,X15) != X14
        | ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k2_tarski(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X15)
        | esk1_3(X13,X14,X15) = X13
        | esk1_3(X13,X14,X15) = X14
        | X15 = k2_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_30,plain,(
    ! [X46,X47,X48,X49] :
      ( ~ v1_funct_1(X49)
      | ~ v1_funct_2(X49,X46,X47)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
      | ~ r2_hidden(X48,X46)
      | X47 = k1_xboole_0
      | r2_hidden(k1_funct_1(X49,X48),k2_relset_1(X46,X47,X49)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_funct_2])])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_35,plain,(
    ! [X25,X26] :
      ( ~ r2_hidden(X25,X26)
      | m1_subset_1(k1_tarski(X25),k1_zfmisc_1(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

cnf(c_0_36,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),k2_relset_1(X2,X3,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_2(esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( k2_relset_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0,esk5_0) = k2_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_27]),c_0_28])).

fof(c_0_42,plain,(
    ! [X37,X38,X39] :
      ( ( v4_relat_1(X39,X37)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( v5_relat_1(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_43,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | v1_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_44,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,X1),k2_relat_1(esk5_0))
    | ~ r2_hidden(X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),c_0_33])]),c_0_40])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).

fof(c_0_47,plain,(
    ! [X23,X24] :
      ( ( ~ r1_tarski(X23,k1_tarski(X24))
        | X23 = k1_xboole_0
        | X23 = k1_tarski(X24) )
      & ( X23 != k1_xboole_0
        | r1_tarski(X23,k1_tarski(X24)) )
      & ( X23 != k1_tarski(X24)
        | r1_tarski(X23,k1_tarski(X24)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

fof(c_0_48,plain,(
    ! [X29,X30] :
      ( ( ~ v4_relat_1(X30,X29)
        | r1_tarski(k1_relat_1(X30),X29)
        | ~ v1_relat_1(X30) )
      & ( ~ r1_tarski(k1_relat_1(X30),X29)
        | v4_relat_1(X30,X29)
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_49,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_51,plain,(
    ! [X27,X28] :
      ( ( ~ m1_subset_1(X27,k1_zfmisc_1(X28))
        | r1_tarski(X27,X28) )
      & ( ~ r1_tarski(X27,X28)
        | m1_subset_1(X27,k1_zfmisc_1(X28)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_52,plain,
    ( m1_subset_1(k2_enumset1(X1,X1,X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk3_0),k2_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( k2_relset_1(k1_tarski(esk3_0),esk4_0,esk5_0) != k1_tarski(k1_funct_1(esk5_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_55,plain,(
    ! [X43,X45] :
      ( v1_relat_1(esk2_1(X43))
      & v1_funct_1(esk2_1(X43))
      & k1_relat_1(esk2_1(X43)) = X43
      & ( ~ r2_hidden(X45,X43)
        | k1_funct_1(esk2_1(X43),X45) = k1_tarski(X45) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e15_31__wellord2])])])])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( v4_relat_1(esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_33])).

cnf(c_0_60,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_33])).

fof(c_0_61,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(k2_enumset1(k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0)),k1_zfmisc_1(k2_relat_1(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_64,negated_conjecture,
    ( k2_relset_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0,esk5_0) != k2_enumset1(k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_65,plain,
    ( k1_funct_1(esk2_1(X2),X1) = k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_27]),c_0_28])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | ~ r1_tarski(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk5_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])])).

cnf(c_0_69,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k2_enumset1(k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0)),k2_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( k2_enumset1(k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0)) != k2_relat_1(esk5_0) ),
    inference(rw,[status(thm)],[c_0_64,c_0_38])).

cnf(c_0_72,plain,
    ( k1_funct_1(esk2_1(X2),X1) = k2_enumset1(X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_26]),c_0_27]),c_0_28])).

fof(c_0_73,plain,(
    ! [X31] :
      ( ( k1_relat_1(X31) != k1_xboole_0
        | X31 = k1_xboole_0
        | ~ v1_relat_1(X31) )
      & ( k2_relat_1(X31) != k1_xboole_0
        | X31 = k1_xboole_0
        | ~ v1_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_66])])).

cnf(c_0_75,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = k1_relat_1(esk5_0)
    | k1_relat_1(esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk5_0),k2_enumset1(k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( k2_enumset1(k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0)) = k1_funct_1(esk2_1(k2_relat_1(esk5_0)),k1_funct_1(esk5_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_53])).

cnf(c_0_78,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | r2_hidden(esk3_0,k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,plain,
    ( k1_relat_1(esk2_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_81,plain,
    ( v1_relat_1(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_82,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk5_0),k1_funct_1(esk2_1(k2_relat_1(esk5_0)),k1_funct_1(esk5_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk3_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_60])])).

cnf(c_0_85,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_86,plain,
    ( esk2_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_80]),c_0_81])])])).

cnf(c_0_87,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85]),c_0_85]),c_0_86]),c_0_87])])).

cnf(c_0_89,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = k1_funct_1(esk2_1(k1_relat_1(esk5_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_88])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(k1_funct_1(esk2_1(k1_relat_1(esk5_0)),esk3_0),k1_zfmisc_1(k1_relat_1(esk5_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_88]),c_0_89])).

fof(c_0_91,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ v1_funct_1(X33)
      | k1_relat_1(X33) != k1_tarski(X32)
      | k2_relat_1(X33) = k1_tarski(k1_funct_1(X33,X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k1_funct_1(esk2_1(k1_relat_1(esk5_0)),esk3_0),k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk5_0),k1_funct_1(esk2_1(k1_relat_1(esk5_0)),esk3_0)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_89])).

cnf(c_0_94,plain,
    ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X1) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( k1_funct_1(esk2_1(k1_relat_1(esk5_0)),esk3_0) = k1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_92]),c_0_93])])).

cnf(c_0_96,plain,
    ( k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))
    | k1_relat_1(X1) != k2_enumset1(X2,X2,X2,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_97,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = k1_relat_1(esk5_0) ),
    inference(rw,[status(thm)],[c_0_89,c_0_95])).

cnf(c_0_98,negated_conjecture,
    ( k2_enumset1(k1_funct_1(X1,esk3_0),k1_funct_1(X1,esk3_0),k1_funct_1(X1,esk3_0),k1_funct_1(X1,esk3_0)) = k2_relat_1(X1)
    | k1_relat_1(X1) != k1_relat_1(esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_99,negated_conjecture,
    ( k1_funct_1(esk2_1(k2_relat_1(esk5_0)),k1_funct_1(esk5_0,esk3_0)) != k2_relat_1(esk5_0) ),
    inference(rw,[status(thm)],[c_0_71,c_0_77])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_98]),c_0_77]),c_0_39]),c_0_60])]),c_0_99]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:35:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C12_02_nc_F1_SE_CS_SP_PS_S002A
% 0.12/0.38  # and selection function SelectNegativeLiterals.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.028 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t62_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>k2_relset_1(k1_tarski(X1),X2,X3)=k1_tarski(k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 0.12/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.38  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.12/0.38  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.12/0.38  fof(t6_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 0.12/0.38  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 0.12/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.12/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.12/0.38  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.12/0.38  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.12/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.12/0.38  fof(s3_funct_1__e15_31__wellord2, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_tarski(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e15_31__wellord2)).
% 0.12/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.38  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.12/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.38  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.12/0.38  fof(t14_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 0.12/0.38  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>k2_relset_1(k1_tarski(X1),X2,X3)=k1_tarski(k1_funct_1(X3,X1))))), inference(assume_negation,[status(cth)],[t62_funct_2])).
% 0.12/0.38  fof(c_0_20, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))))&(esk4_0!=k1_xboole_0&k2_relset_1(k1_tarski(esk3_0),esk4_0,esk5_0)!=k1_tarski(k1_funct_1(esk5_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.12/0.38  fof(c_0_21, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.38  fof(c_0_22, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.38  fof(c_0_23, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.38  fof(c_0_24, plain, ![X40, X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|k2_relset_1(X40,X41,X42)=k2_relat_1(X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_26, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.38  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.38  fof(c_0_29, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X11,X10)|(X11=X8|X11=X9)|X10!=k2_tarski(X8,X9))&((X12!=X8|r2_hidden(X12,X10)|X10!=k2_tarski(X8,X9))&(X12!=X9|r2_hidden(X12,X10)|X10!=k2_tarski(X8,X9))))&(((esk1_3(X13,X14,X15)!=X13|~r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k2_tarski(X13,X14))&(esk1_3(X13,X14,X15)!=X14|~r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k2_tarski(X13,X14)))&(r2_hidden(esk1_3(X13,X14,X15),X15)|(esk1_3(X13,X14,X15)=X13|esk1_3(X13,X14,X15)=X14)|X15=k2_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.12/0.38  fof(c_0_30, plain, ![X46, X47, X48, X49]:(~v1_funct_1(X49)|~v1_funct_2(X49,X46,X47)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))|(~r2_hidden(X48,X46)|(X47=k1_xboole_0|r2_hidden(k1_funct_1(X49,X48),k2_relset_1(X46,X47,X49))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_funct_2])])).
% 0.12/0.38  cnf(c_0_31, negated_conjecture, (v1_funct_2(esk5_0,k1_tarski(esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_32, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.38  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])).
% 0.12/0.38  cnf(c_0_34, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.38  fof(c_0_35, plain, ![X25, X26]:(~r2_hidden(X25,X26)|m1_subset_1(k1_tarski(X25),k1_zfmisc_1(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.12/0.38  cnf(c_0_36, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),k2_relset_1(X2,X3,X1))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.38  cnf(c_0_37, negated_conjecture, (v1_funct_2(esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_26]), c_0_27]), c_0_28])).
% 0.12/0.38  cnf(c_0_38, negated_conjecture, (k2_relset_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0,esk5_0)=k2_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.12/0.38  cnf(c_0_39, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_40, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_41, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_27]), c_0_28])).
% 0.12/0.38  fof(c_0_42, plain, ![X37, X38, X39]:((v4_relat_1(X39,X37)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(v5_relat_1(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.12/0.38  fof(c_0_43, plain, ![X34, X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|v1_relat_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.12/0.38  cnf(c_0_44, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.38  cnf(c_0_45, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,X1),k2_relat_1(esk5_0))|~r2_hidden(X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), c_0_33])]), c_0_40])).
% 0.12/0.38  cnf(c_0_46, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).
% 0.12/0.38  fof(c_0_47, plain, ![X23, X24]:((~r1_tarski(X23,k1_tarski(X24))|(X23=k1_xboole_0|X23=k1_tarski(X24)))&((X23!=k1_xboole_0|r1_tarski(X23,k1_tarski(X24)))&(X23!=k1_tarski(X24)|r1_tarski(X23,k1_tarski(X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.12/0.38  fof(c_0_48, plain, ![X29, X30]:((~v4_relat_1(X30,X29)|r1_tarski(k1_relat_1(X30),X29)|~v1_relat_1(X30))&(~r1_tarski(k1_relat_1(X30),X29)|v4_relat_1(X30,X29)|~v1_relat_1(X30))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.12/0.38  cnf(c_0_49, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.12/0.38  cnf(c_0_50, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.12/0.38  fof(c_0_51, plain, ![X27, X28]:((~m1_subset_1(X27,k1_zfmisc_1(X28))|r1_tarski(X27,X28))&(~r1_tarski(X27,X28)|m1_subset_1(X27,k1_zfmisc_1(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.12/0.38  cnf(c_0_52, plain, (m1_subset_1(k2_enumset1(X1,X1,X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_26]), c_0_27]), c_0_28])).
% 0.12/0.38  cnf(c_0_53, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,esk3_0),k2_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.12/0.38  cnf(c_0_54, negated_conjecture, (k2_relset_1(k1_tarski(esk3_0),esk4_0,esk5_0)!=k1_tarski(k1_funct_1(esk5_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  fof(c_0_55, plain, ![X43, X45]:(((v1_relat_1(esk2_1(X43))&v1_funct_1(esk2_1(X43)))&k1_relat_1(esk2_1(X43))=X43)&(~r2_hidden(X45,X43)|k1_funct_1(esk2_1(X43),X45)=k1_tarski(X45))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e15_31__wellord2])])])])).
% 0.12/0.38  cnf(c_0_56, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.38  cnf(c_0_57, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.12/0.38  cnf(c_0_58, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.38  cnf(c_0_59, negated_conjecture, (v4_relat_1(esk5_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_49, c_0_33])).
% 0.12/0.38  cnf(c_0_60, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_50, c_0_33])).
% 0.12/0.38  fof(c_0_61, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.38  cnf(c_0_62, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.12/0.38  cnf(c_0_63, negated_conjecture, (m1_subset_1(k2_enumset1(k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0)),k1_zfmisc_1(k2_relat_1(esk5_0)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.12/0.38  cnf(c_0_64, negated_conjecture, (k2_relset_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),esk4_0,esk5_0)!=k2_enumset1(k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28])).
% 0.12/0.38  cnf(c_0_65, plain, (k1_funct_1(esk2_1(X2),X1)=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.12/0.38  cnf(c_0_66, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_27]), c_0_28])).
% 0.12/0.38  cnf(c_0_67, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|~r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28])).
% 0.12/0.38  cnf(c_0_68, negated_conjecture, (r1_tarski(k1_relat_1(esk5_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])])).
% 0.12/0.38  cnf(c_0_69, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.12/0.38  cnf(c_0_70, negated_conjecture, (r1_tarski(k2_enumset1(k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0)),k2_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.12/0.38  cnf(c_0_71, negated_conjecture, (k2_enumset1(k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0))!=k2_relat_1(esk5_0)), inference(rw,[status(thm)],[c_0_64, c_0_38])).
% 0.12/0.38  cnf(c_0_72, plain, (k1_funct_1(esk2_1(X2),X1)=k2_enumset1(X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_26]), c_0_27]), c_0_28])).
% 0.12/0.38  fof(c_0_73, plain, ![X31]:((k1_relat_1(X31)!=k1_xboole_0|X31=k1_xboole_0|~v1_relat_1(X31))&(k2_relat_1(X31)!=k1_xboole_0|X31=k1_xboole_0|~v1_relat_1(X31))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.12/0.38  cnf(c_0_74, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_66])])).
% 0.12/0.38  cnf(c_0_75, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=k1_relat_1(esk5_0)|k1_relat_1(esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.12/0.38  cnf(c_0_76, negated_conjecture, (~r1_tarski(k2_relat_1(esk5_0),k2_enumset1(k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])).
% 0.12/0.38  cnf(c_0_77, negated_conjecture, (k2_enumset1(k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0),k1_funct_1(esk5_0,esk3_0))=k1_funct_1(esk2_1(k2_relat_1(esk5_0)),k1_funct_1(esk5_0,esk3_0))), inference(spm,[status(thm)],[c_0_72, c_0_53])).
% 0.12/0.38  cnf(c_0_78, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.12/0.38  cnf(c_0_79, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|r2_hidden(esk3_0,k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.12/0.38  cnf(c_0_80, plain, (k1_relat_1(esk2_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.12/0.38  cnf(c_0_81, plain, (v1_relat_1(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.12/0.38  fof(c_0_82, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.38  cnf(c_0_83, negated_conjecture, (~r1_tarski(k2_relat_1(esk5_0),k1_funct_1(esk2_1(k2_relat_1(esk5_0)),k1_funct_1(esk5_0,esk3_0)))), inference(rw,[status(thm)],[c_0_76, c_0_77])).
% 0.12/0.38  cnf(c_0_84, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk3_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_60])])).
% 0.12/0.38  cnf(c_0_85, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.12/0.38  cnf(c_0_86, plain, (esk2_1(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_80]), c_0_81])])])).
% 0.12/0.38  cnf(c_0_87, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.12/0.38  cnf(c_0_88, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85]), c_0_85]), c_0_86]), c_0_87])])).
% 0.12/0.38  cnf(c_0_89, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=k1_funct_1(esk2_1(k1_relat_1(esk5_0)),esk3_0)), inference(spm,[status(thm)],[c_0_72, c_0_88])).
% 0.12/0.38  cnf(c_0_90, negated_conjecture, (m1_subset_1(k1_funct_1(esk2_1(k1_relat_1(esk5_0)),esk3_0),k1_zfmisc_1(k1_relat_1(esk5_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_88]), c_0_89])).
% 0.12/0.38  fof(c_0_91, plain, ![X32, X33]:(~v1_relat_1(X33)|~v1_funct_1(X33)|(k1_relat_1(X33)!=k1_tarski(X32)|k2_relat_1(X33)=k1_tarski(k1_funct_1(X33,X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).
% 0.12/0.38  cnf(c_0_92, negated_conjecture, (r1_tarski(k1_funct_1(esk2_1(k1_relat_1(esk5_0)),esk3_0),k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_62, c_0_90])).
% 0.12/0.38  cnf(c_0_93, negated_conjecture, (r1_tarski(k1_relat_1(esk5_0),k1_funct_1(esk2_1(k1_relat_1(esk5_0)),esk3_0))), inference(rw,[status(thm)],[c_0_68, c_0_89])).
% 0.12/0.38  cnf(c_0_94, plain, (k2_relat_1(X1)=k1_tarski(k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|k1_relat_1(X1)!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.12/0.38  cnf(c_0_95, negated_conjecture, (k1_funct_1(esk2_1(k1_relat_1(esk5_0)),esk3_0)=k1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_92]), c_0_93])])).
% 0.12/0.38  cnf(c_0_96, plain, (k2_relat_1(X1)=k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))|k1_relat_1(X1)!=k2_enumset1(X2,X2,X2,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28])).
% 0.12/0.38  cnf(c_0_97, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=k1_relat_1(esk5_0)), inference(rw,[status(thm)],[c_0_89, c_0_95])).
% 0.12/0.38  cnf(c_0_98, negated_conjecture, (k2_enumset1(k1_funct_1(X1,esk3_0),k1_funct_1(X1,esk3_0),k1_funct_1(X1,esk3_0),k1_funct_1(X1,esk3_0))=k2_relat_1(X1)|k1_relat_1(X1)!=k1_relat_1(esk5_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.12/0.38  cnf(c_0_99, negated_conjecture, (k1_funct_1(esk2_1(k2_relat_1(esk5_0)),k1_funct_1(esk5_0,esk3_0))!=k2_relat_1(esk5_0)), inference(rw,[status(thm)],[c_0_71, c_0_77])).
% 0.12/0.38  cnf(c_0_100, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_98]), c_0_77]), c_0_39]), c_0_60])]), c_0_99]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 101
% 0.12/0.38  # Proof object clause steps            : 63
% 0.12/0.38  # Proof object formula steps           : 38
% 0.12/0.38  # Proof object conjectures             : 36
% 0.12/0.38  # Proof object clause conjectures      : 33
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 26
% 0.12/0.38  # Proof object initial formulas used   : 19
% 0.12/0.38  # Proof object generating inferences   : 21
% 0.12/0.38  # Proof object simplifying inferences  : 69
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 19
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 40
% 0.12/0.38  # Removed in clause preprocessing      : 3
% 0.12/0.38  # Initial clauses in saturation        : 37
% 0.12/0.38  # Processed clauses                    : 208
% 0.12/0.38  # ...of these trivial                  : 10
% 0.12/0.38  # ...subsumed                          : 11
% 0.12/0.38  # ...remaining for further processing  : 187
% 0.12/0.38  # Other redundant clauses eliminated   : 19
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 4
% 0.12/0.38  # Backward-rewritten                   : 38
% 0.12/0.38  # Generated clauses                    : 550
% 0.12/0.38  # ...of the previous two non-trivial   : 387
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 529
% 0.12/0.38  # Factorizations                       : 3
% 0.12/0.38  # Equation resolutions                 : 20
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 104
% 0.12/0.38  #    Positive orientable unit clauses  : 59
% 0.12/0.38  #    Positive unorientable unit clauses: 1
% 0.12/0.38  #    Negative unit clauses             : 3
% 0.12/0.38  #    Non-unit-clauses                  : 41
% 0.12/0.38  # Current number of unprocessed clauses: 197
% 0.12/0.38  # ...number of literals in the above   : 720
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 79
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 315
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 158
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 10
% 0.12/0.38  # Unit Clause-clause subsumption calls : 260
% 0.12/0.38  # Rewrite failures with RHS unbound    : 15
% 0.12/0.38  # BW rewrite match attempts            : 44
% 0.12/0.38  # BW rewrite match successes           : 14
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 9594
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.041 s
% 0.12/0.38  # System time              : 0.006 s
% 0.12/0.38  # Total time               : 0.047 s
% 0.12/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
