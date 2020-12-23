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
% DateTime   : Thu Dec  3 11:04:17 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 194 expanded)
%              Number of clauses        :   41 (  80 expanded)
%              Number of leaves         :   15 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  181 ( 463 expanded)
%              Number of equality atoms :   43 ( 141 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t61_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k1_tarski(X1),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => r2_hidden(k1_funct_1(X3,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(t6_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(t172_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => r2_hidden(k1_funct_1(X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r2_hidden(k1_funct_1(X3,X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t61_funct_2])).

fof(c_0_16,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,k1_tarski(esk1_0),esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),esk2_0)))
    & esk2_0 != k1_xboole_0
    & ~ r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_17,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X27,X28,X29] :
      ( ( v4_relat_1(X29,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( v5_relat_1(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | v1_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_24,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | k2_relset_1(X30,X31,X32) = k2_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_25,plain,(
    ! [X13,X14,X15] :
      ( ( r2_hidden(X13,X15)
        | ~ r1_tarski(k2_tarski(X13,X14),X15) )
      & ( r2_hidden(X14,X15)
        | ~ r1_tarski(k2_tarski(X13,X14),X15) )
      & ( ~ r2_hidden(X13,X15)
        | ~ r2_hidden(X14,X15)
        | r1_tarski(k2_tarski(X13,X14),X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_26,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_27,plain,(
    ! [X11,X12] :
      ( ( ~ r1_tarski(X11,k1_tarski(X12))
        | X11 = k1_xboole_0
        | X11 = k1_tarski(X12) )
      & ( X11 != k1_xboole_0
        | r1_tarski(X11,k1_tarski(X12)) )
      & ( X11 != k1_tarski(X12)
        | r1_tarski(X11,k1_tarski(X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

fof(c_0_28,plain,(
    ! [X16,X17] :
      ( ( ~ v4_relat_1(X17,X16)
        | r1_tarski(k1_relat_1(X17),X16)
        | ~ v1_relat_1(X17) )
      & ( ~ r1_tarski(k1_relat_1(X17),X16)
        | v4_relat_1(X17,X16)
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_29,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk1_0),esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_31,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X33,X34,X35,X36] :
      ( ~ v1_funct_1(X36)
      | ~ v1_funct_2(X36,X33,X34)
      | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | ~ r2_hidden(X35,X33)
      | X34 = k1_xboole_0
      | r2_hidden(k1_funct_1(X36,X35),k2_relset_1(X33,X34,X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_funct_2])])).

cnf(c_0_33,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk3_0,k1_tarski(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( v4_relat_1(esk3_0,k1_enumset1(esk1_0,esk1_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

fof(c_0_41,plain,(
    ! [X19,X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ v5_relat_1(X20,X19)
      | ~ v1_funct_1(X20)
      | ~ r2_hidden(X21,k1_relat_1(X20))
      | r2_hidden(k1_funct_1(X20,X21),X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).

cnf(c_0_42,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_43,plain,(
    ! [X22,X23] :
      ( ~ r2_hidden(X22,X23)
      | ~ r1_tarski(X23,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_44,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),k2_relset_1(X2,X3,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( k2_relset_1(k1_enumset1(esk1_0,esk1_0,esk1_0),esk2_0,esk3_0) = k2_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_2(esk3_0,k1_enumset1(esk1_0,esk1_0,esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_21]),c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_48,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_enumset1(X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_22])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_enumset1(X2,X2,X2)
    | ~ r1_tarski(X1,k1_enumset1(X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_21]),c_0_21]),c_0_22]),c_0_22])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),k1_enumset1(esk1_0,esk1_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_54,plain,
    ( r2_hidden(k1_funct_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_55,negated_conjecture,
    ( v5_relat_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_30])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,X1),k2_relat_1(esk3_0))
    | ~ r2_hidden(X1,k1_enumset1(esk1_0,esk1_0,esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_30]),c_0_45]),c_0_46]),c_0_47])]),c_0_48])).

fof(c_0_58,plain,(
    ! [X18] :
      ( ( k1_relat_1(X18) != k1_xboole_0
        | k2_relat_1(X18) = k1_xboole_0
        | ~ v1_relat_1(X18) )
      & ( k2_relat_1(X18) != k1_xboole_0
        | k1_relat_1(X18) = k1_xboole_0
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

fof(c_0_59,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( k1_enumset1(esk1_0,esk1_0,esk1_0) = k1_relat_1(esk3_0)
    | k1_relat_1(esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_47]),c_0_55]),c_0_40])])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_hidden(X1,k1_enumset1(esk1_0,esk1_0,esk1_0))
    | ~ r1_tarski(k2_relat_1(esk3_0),k1_funct_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_enumset1(X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[c_0_63,c_0_22])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_hidden(X1,k1_enumset1(esk1_0,esk1_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_67]),c_0_40])])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X1)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_50])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_69,c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:18:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t61_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 0.12/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.37  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.12/0.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.12/0.37  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.12/0.37  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.12/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.37  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.12/0.37  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.12/0.37  fof(t6_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 0.12/0.37  fof(t172_funct_1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 0.12/0.37  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.12/0.37  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 0.12/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.37  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2)))), inference(assume_negation,[status(cth)],[t61_funct_2])).
% 0.12/0.37  fof(c_0_16, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,k1_tarski(esk1_0),esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),esk2_0))))&(esk2_0!=k1_xboole_0&~r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.12/0.37  fof(c_0_17, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.37  fof(c_0_18, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.37  fof(c_0_19, plain, ![X27, X28, X29]:((v4_relat_1(X29,X27)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(v5_relat_1(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_21, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.37  fof(c_0_23, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|v1_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.12/0.37  fof(c_0_24, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|k2_relset_1(X30,X31,X32)=k2_relat_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.12/0.37  fof(c_0_25, plain, ![X13, X14, X15]:(((r2_hidden(X13,X15)|~r1_tarski(k2_tarski(X13,X14),X15))&(r2_hidden(X14,X15)|~r1_tarski(k2_tarski(X13,X14),X15)))&(~r2_hidden(X13,X15)|~r2_hidden(X14,X15)|r1_tarski(k2_tarski(X13,X14),X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.12/0.37  fof(c_0_26, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.37  fof(c_0_27, plain, ![X11, X12]:((~r1_tarski(X11,k1_tarski(X12))|(X11=k1_xboole_0|X11=k1_tarski(X12)))&((X11!=k1_xboole_0|r1_tarski(X11,k1_tarski(X12)))&(X11!=k1_tarski(X12)|r1_tarski(X11,k1_tarski(X12))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.12/0.37  fof(c_0_28, plain, ![X16, X17]:((~v4_relat_1(X17,X16)|r1_tarski(k1_relat_1(X17),X16)|~v1_relat_1(X17))&(~r1_tarski(k1_relat_1(X17),X16)|v4_relat_1(X17,X16)|~v1_relat_1(X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.12/0.37  cnf(c_0_29, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk1_0),esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.12/0.37  cnf(c_0_31, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.37  fof(c_0_32, plain, ![X33, X34, X35, X36]:(~v1_funct_1(X36)|~v1_funct_2(X36,X33,X34)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|(~r2_hidden(X35,X33)|(X34=k1_xboole_0|r2_hidden(k1_funct_1(X36,X35),k2_relset_1(X33,X34,X36))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_funct_2])])).
% 0.12/0.37  cnf(c_0_33, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk3_0,k1_tarski(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_35, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_36, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.37  cnf(c_0_37, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.37  cnf(c_0_38, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.37  cnf(c_0_39, negated_conjecture, (v4_relat_1(esk3_0,k1_enumset1(esk1_0,esk1_0,esk1_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_30])).
% 0.12/0.37  fof(c_0_41, plain, ![X19, X20, X21]:(~v1_relat_1(X20)|~v5_relat_1(X20,X19)|~v1_funct_1(X20)|(~r2_hidden(X21,k1_relat_1(X20))|r2_hidden(k1_funct_1(X20,X21),X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).
% 0.12/0.37  cnf(c_0_42, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.37  fof(c_0_43, plain, ![X22, X23]:(~r2_hidden(X22,X23)|~r1_tarski(X23,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.12/0.37  cnf(c_0_44, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),k2_relset_1(X2,X3,X1))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_45, negated_conjecture, (k2_relset_1(k1_enumset1(esk1_0,esk1_0,esk1_0),esk2_0,esk3_0)=k2_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_30])).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, (v1_funct_2(esk3_0,k1_enumset1(esk1_0,esk1_0,esk1_0),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_21]), c_0_22])).
% 0.12/0.37  cnf(c_0_47, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_48, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_49, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_enumset1(X1,X1,X3),X2)), inference(rw,[status(thm)],[c_0_35, c_0_22])).
% 0.12/0.37  cnf(c_0_50, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_36])).
% 0.12/0.37  cnf(c_0_51, plain, (X1=k1_xboole_0|X1=k1_enumset1(X2,X2,X2)|~r1_tarski(X1,k1_enumset1(X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_21]), c_0_21]), c_0_22]), c_0_22])).
% 0.12/0.37  cnf(c_0_52, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),k1_enumset1(esk1_0,esk1_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.12/0.37  cnf(c_0_53, negated_conjecture, (~r2_hidden(k1_funct_1(esk3_0,esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_54, plain, (r2_hidden(k1_funct_1(X1,X3),X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.12/0.37  cnf(c_0_55, negated_conjecture, (v5_relat_1(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_42, c_0_30])).
% 0.12/0.37  cnf(c_0_56, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.12/0.37  cnf(c_0_57, negated_conjecture, (r2_hidden(k1_funct_1(esk3_0,X1),k2_relat_1(esk3_0))|~r2_hidden(X1,k1_enumset1(esk1_0,esk1_0,esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_30]), c_0_45]), c_0_46]), c_0_47])]), c_0_48])).
% 0.12/0.37  fof(c_0_58, plain, ![X18]:((k1_relat_1(X18)!=k1_xboole_0|k2_relat_1(X18)=k1_xboole_0|~v1_relat_1(X18))&(k2_relat_1(X18)!=k1_xboole_0|k1_relat_1(X18)=k1_xboole_0|~v1_relat_1(X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.12/0.37  fof(c_0_59, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.37  cnf(c_0_60, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X2))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.12/0.37  cnf(c_0_61, negated_conjecture, (k1_enumset1(esk1_0,esk1_0,esk1_0)=k1_relat_1(esk3_0)|k1_relat_1(esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.12/0.37  cnf(c_0_62, negated_conjecture, (~r2_hidden(esk1_0,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_47]), c_0_55]), c_0_40])])).
% 0.12/0.37  cnf(c_0_63, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_64, negated_conjecture, (~r2_hidden(X1,k1_enumset1(esk1_0,esk1_0,esk1_0))|~r1_tarski(k2_relat_1(esk3_0),k1_funct_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.12/0.37  cnf(c_0_65, plain, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.12/0.37  cnf(c_0_66, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.12/0.37  cnf(c_0_67, negated_conjecture, (k1_relat_1(esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.12/0.37  cnf(c_0_68, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_enumset1(X3,X3,X1),X2)), inference(rw,[status(thm)],[c_0_63, c_0_22])).
% 0.12/0.37  cnf(c_0_69, negated_conjecture, (~r2_hidden(X1,k1_enumset1(esk1_0,esk1_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_67]), c_0_40])])).
% 0.12/0.37  cnf(c_0_70, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X1))), inference(spm,[status(thm)],[c_0_68, c_0_50])).
% 0.12/0.37  cnf(c_0_71, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_69, c_0_70]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 72
% 0.12/0.37  # Proof object clause steps            : 41
% 0.12/0.37  # Proof object formula steps           : 31
% 0.12/0.37  # Proof object conjectures             : 22
% 0.12/0.37  # Proof object clause conjectures      : 19
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 21
% 0.12/0.37  # Proof object initial formulas used   : 15
% 0.12/0.37  # Proof object generating inferences   : 14
% 0.12/0.37  # Proof object simplifying inferences  : 27
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 15
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 28
% 0.12/0.37  # Removed in clause preprocessing      : 2
% 0.12/0.37  # Initial clauses in saturation        : 26
% 0.12/0.37  # Processed clauses                    : 78
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 4
% 0.12/0.37  # ...remaining for further processing  : 74
% 0.12/0.37  # Other redundant clauses eliminated   : 4
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 5
% 0.12/0.37  # Generated clauses                    : 54
% 0.12/0.37  # ...of the previous two non-trivial   : 46
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 50
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 4
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 42
% 0.12/0.37  #    Positive orientable unit clauses  : 12
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 6
% 0.12/0.37  #    Non-unit-clauses                  : 24
% 0.12/0.37  # Current number of unprocessed clauses: 8
% 0.12/0.37  # ...number of literals in the above   : 35
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 30
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 165
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 42
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.12/0.37  # Unit Clause-clause subsumption calls : 11
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 6
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 2528
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.031 s
% 0.12/0.37  # System time              : 0.004 s
% 0.12/0.37  # Total time               : 0.035 s
% 0.12/0.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
