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
% DateTime   : Thu Dec  3 11:04:17 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   91 (1373 expanded)
%              Number of clauses        :   53 ( 560 expanded)
%              Number of leaves         :   19 ( 380 expanded)
%              Depth                    :   15
%              Number of atoms          :  208 (2844 expanded)
%              Number of equality atoms :   53 (1048 expanded)
%              Maximal formula depth    :   10 (   3 average)
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

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

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

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

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

fof(t172_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => r2_hidden(k1_funct_1(X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(fc9_relat_1,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ~ v1_xboole_0(k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t6_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r2_hidden(k1_funct_1(X3,X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t61_funct_2])).

fof(c_0_20,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,k1_tarski(esk2_0),esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0)))
    & esk3_0 != k1_xboole_0
    & ~ r2_hidden(k1_funct_1(esk4_0,esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_21,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X15,X16,X17] : k2_enumset1(X15,X15,X16,X17) = k1_enumset1(X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X33,X34,X35] :
      ( ( v4_relat_1(X35,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( v5_relat_1(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))) ),
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
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | v1_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_30,plain,(
    ! [X19,X20] :
      ( ( ~ r1_tarski(k1_tarski(X19),X20)
        | r2_hidden(X19,X20) )
      & ( ~ r2_hidden(X19,X20)
        | r1_tarski(k1_tarski(X19),X20) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_31,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_32,plain,(
    ! [X21,X22] :
      ( ( ~ r1_tarski(X21,k1_tarski(X22))
        | X21 = k1_xboole_0
        | X21 = k1_tarski(X22) )
      & ( X21 != k1_xboole_0
        | r1_tarski(X21,k1_tarski(X22)) )
      & ( X21 != k1_tarski(X22)
        | r1_tarski(X21,k1_tarski(X22)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

fof(c_0_33,plain,(
    ! [X23,X24] :
      ( ( ~ v4_relat_1(X24,X23)
        | r1_tarski(k1_relat_1(X24),X23)
        | ~ v1_relat_1(X24) )
      & ( ~ r1_tarski(k1_relat_1(X24),X23)
        | v4_relat_1(X24,X23)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_34,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_36,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( v4_relat_1(esk4_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_35])).

fof(c_0_43,plain,(
    ! [X27,X28,X29] :
      ( ~ v1_relat_1(X28)
      | ~ v5_relat_1(X28,X27)
      | ~ v1_funct_1(X28)
      | ~ r2_hidden(X29,k1_relat_1(X28))
      | r2_hidden(k1_funct_1(X28,X29),X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).

cnf(c_0_44,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_45,plain,(
    ! [X25] :
      ( v1_xboole_0(X25)
      | ~ v1_relat_1(X25)
      | ~ v1_xboole_0(k2_relat_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_relat_1])])])).

fof(c_0_46,plain,(
    ! [X26] :
      ( ( k1_relat_1(X26) != k1_xboole_0
        | k2_relat_1(X26) = k1_xboole_0
        | ~ v1_relat_1(X26) )
      & ( k2_relat_1(X26) != k1_xboole_0
        | k1_relat_1(X26) = k1_xboole_0
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_enumset1(X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | ~ r1_tarski(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk4_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_52,plain,
    ( r2_hidden(k1_funct_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_54,negated_conjecture,
    ( v5_relat_1(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_35])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0) = k1_relat_1(esk4_0)
    | k1_relat_1(esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54]),c_0_42])])).

fof(c_0_61,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(X9)
      | X9 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_62,plain,
    ( v1_xboole_0(X1)
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_63,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

fof(c_0_64,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k2_relset_1(X36,X37,X38) = k2_relat_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_65,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_42])])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_tarski(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_68,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_69,plain,(
    ! [X39,X40,X41,X42] :
      ( ~ v1_funct_1(X42)
      | ~ v1_funct_2(X42,X39,X40)
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | ~ r2_hidden(X41,X39)
      | X40 = k1_xboole_0
      | r2_hidden(k1_funct_1(X42,X41),k2_relset_1(X39,X40,X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_funct_2])])).

cnf(c_0_70,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_2(esk4_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_72,negated_conjecture,
    ( k2_relset_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk4_0) = k2_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_35])).

fof(c_0_73,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_74,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),k2_relset_1(X2,X3,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_71,c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_79,negated_conjecture,
    ( k2_relset_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_70]),c_0_70])).

fof(c_0_80,plain,(
    ! [X18] : ~ v1_xboole_0(k1_tarski(X18)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_81,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(k1_funct_1(k1_xboole_0,X1),k2_relat_1(k1_xboole_0))
    | ~ r2_hidden(X1,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76]),c_0_77])]),c_0_78]),c_0_79])).

cnf(c_0_83,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_hidden(X1,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))
    | ~ v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_85,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_86,plain,
    ( ~ v1_xboole_0(k2_enumset1(X1,X1,X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_87,negated_conjecture,
    ( ~ v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])).

cnf(c_0_88,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_63,c_0_70])).

cnf(c_0_89,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_42,c_0_70])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_56]),c_0_57]),c_0_88]),c_0_89])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:28:19 EST 2020
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
% 0.12/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.37  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.12/0.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.12/0.37  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.12/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.37  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.12/0.37  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.12/0.37  fof(t172_funct_1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 0.12/0.37  fof(fc9_relat_1, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_relat_1(X1))=>~(v1_xboole_0(k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 0.12/0.37  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 0.12/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.12/0.37  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.12/0.37  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.12/0.37  fof(t6_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 0.12/0.37  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.12/0.37  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.12/0.37  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2)))), inference(assume_negation,[status(cth)],[t61_funct_2])).
% 0.12/0.37  fof(c_0_20, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,k1_tarski(esk2_0),esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))))&(esk3_0!=k1_xboole_0&~r2_hidden(k1_funct_1(esk4_0,esk2_0),esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.12/0.37  fof(c_0_21, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.37  fof(c_0_22, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.37  fof(c_0_23, plain, ![X15, X16, X17]:k2_enumset1(X15,X15,X16,X17)=k1_enumset1(X15,X16,X17), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.37  fof(c_0_24, plain, ![X33, X34, X35]:((v4_relat_1(X35,X33)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))&(v5_relat_1(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_26, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.37  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.37  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.37  fof(c_0_29, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|v1_relat_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.12/0.37  fof(c_0_30, plain, ![X19, X20]:((~r1_tarski(k1_tarski(X19),X20)|r2_hidden(X19,X20))&(~r2_hidden(X19,X20)|r1_tarski(k1_tarski(X19),X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.12/0.37  fof(c_0_31, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.37  fof(c_0_32, plain, ![X21, X22]:((~r1_tarski(X21,k1_tarski(X22))|(X21=k1_xboole_0|X21=k1_tarski(X22)))&((X21!=k1_xboole_0|r1_tarski(X21,k1_tarski(X22)))&(X21!=k1_tarski(X22)|r1_tarski(X21,k1_tarski(X22))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.12/0.37  fof(c_0_33, plain, ![X23, X24]:((~v4_relat_1(X24,X23)|r1_tarski(k1_relat_1(X24),X23)|~v1_relat_1(X24))&(~r1_tarski(k1_relat_1(X24),X23)|v4_relat_1(X24,X23)|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.12/0.37  cnf(c_0_34, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])).
% 0.12/0.37  cnf(c_0_36, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.37  cnf(c_0_37, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.37  cnf(c_0_38, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.37  cnf(c_0_39, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_40, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (v4_relat_1(esk4_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_35])).
% 0.12/0.37  fof(c_0_43, plain, ![X27, X28, X29]:(~v1_relat_1(X28)|~v5_relat_1(X28,X27)|~v1_funct_1(X28)|(~r2_hidden(X29,k1_relat_1(X28))|r2_hidden(k1_funct_1(X28,X29),X27))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).
% 0.12/0.37  cnf(c_0_44, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  fof(c_0_45, plain, ![X25]:(v1_xboole_0(X25)|~v1_relat_1(X25)|~v1_xboole_0(k2_relat_1(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_relat_1])])])).
% 0.12/0.37  fof(c_0_46, plain, ![X26]:((k1_relat_1(X26)!=k1_xboole_0|k2_relat_1(X26)=k1_xboole_0|~v1_relat_1(X26))&(k2_relat_1(X26)!=k1_xboole_0|k1_relat_1(X26)=k1_xboole_0|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.12/0.37  cnf(c_0_47, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_26]), c_0_27]), c_0_28])).
% 0.12/0.37  cnf(c_0_48, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_38])).
% 0.12/0.37  cnf(c_0_49, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|~r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28])).
% 0.12/0.37  cnf(c_0_50, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.12/0.37  cnf(c_0_51, negated_conjecture, (~r2_hidden(k1_funct_1(esk4_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_52, plain, (r2_hidden(k1_funct_1(X1,X3),X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.12/0.37  cnf(c_0_53, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_54, negated_conjecture, (v5_relat_1(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_44, c_0_35])).
% 0.12/0.37  cnf(c_0_55, plain, (v1_xboole_0(X1)|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.12/0.37  cnf(c_0_56, plain, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.12/0.37  cnf(c_0_57, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.12/0.37  cnf(c_0_58, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.12/0.37  cnf(c_0_59, negated_conjecture, (k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)=k1_relat_1(esk4_0)|k1_relat_1(esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.12/0.37  cnf(c_0_60, negated_conjecture, (~r2_hidden(esk2_0,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54]), c_0_42])])).
% 0.12/0.37  fof(c_0_61, plain, ![X9]:(~v1_xboole_0(X9)|X9=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.12/0.37  cnf(c_0_62, plain, (v1_xboole_0(X1)|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 0.12/0.37  cnf(c_0_63, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 0.12/0.37  fof(c_0_64, plain, ![X36, X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|k2_relset_1(X36,X37,X38)=k2_relat_1(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.12/0.37  cnf(c_0_65, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.12/0.37  cnf(c_0_66, negated_conjecture, (v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_42])])).
% 0.12/0.37  cnf(c_0_67, negated_conjecture, (v1_funct_2(esk4_0,k1_tarski(esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_68, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.12/0.37  fof(c_0_69, plain, ![X39, X40, X41, X42]:(~v1_funct_1(X42)|~v1_funct_2(X42,X39,X40)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|(~r2_hidden(X41,X39)|(X40=k1_xboole_0|r2_hidden(k1_funct_1(X42,X41),k2_relset_1(X39,X40,X42))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_funct_2])])).
% 0.12/0.37  cnf(c_0_70, negated_conjecture, (esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.12/0.37  cnf(c_0_71, negated_conjecture, (v1_funct_2(esk4_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_26]), c_0_27]), c_0_28])).
% 0.12/0.37  cnf(c_0_72, negated_conjecture, (k2_relset_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk4_0)=k2_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_68, c_0_35])).
% 0.12/0.37  fof(c_0_73, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.12/0.37  cnf(c_0_74, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),k2_relset_1(X2,X3,X1))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.12/0.37  cnf(c_0_75, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)))), inference(rw,[status(thm)],[c_0_35, c_0_70])).
% 0.12/0.37  cnf(c_0_76, negated_conjecture, (v1_funct_2(k1_xboole_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)), inference(rw,[status(thm)],[c_0_71, c_0_70])).
% 0.12/0.37  cnf(c_0_77, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_53, c_0_70])).
% 0.12/0.37  cnf(c_0_78, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_79, negated_conjecture, (k2_relset_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,k1_xboole_0)=k2_relat_1(k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_70]), c_0_70])).
% 0.12/0.37  fof(c_0_80, plain, ![X18]:~v1_xboole_0(k1_tarski(X18)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.12/0.37  cnf(c_0_81, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.12/0.37  cnf(c_0_82, negated_conjecture, (r2_hidden(k1_funct_1(k1_xboole_0,X1),k2_relat_1(k1_xboole_0))|~r2_hidden(X1,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76]), c_0_77])]), c_0_78]), c_0_79])).
% 0.12/0.37  cnf(c_0_83, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.12/0.37  cnf(c_0_84, negated_conjecture, (~r2_hidden(X1,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))|~v1_xboole_0(k2_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.12/0.37  cnf(c_0_85, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.12/0.37  cnf(c_0_86, plain, (~v1_xboole_0(k2_enumset1(X1,X1,X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_26]), c_0_27]), c_0_28])).
% 0.12/0.37  cnf(c_0_87, negated_conjecture, (~v1_xboole_0(k2_relat_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])).
% 0.12/0.37  cnf(c_0_88, negated_conjecture, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_63, c_0_70])).
% 0.12/0.37  cnf(c_0_89, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_42, c_0_70])).
% 0.12/0.37  cnf(c_0_90, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_56]), c_0_57]), c_0_88]), c_0_89])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 91
% 0.12/0.37  # Proof object clause steps            : 53
% 0.12/0.37  # Proof object formula steps           : 38
% 0.12/0.37  # Proof object conjectures             : 30
% 0.12/0.37  # Proof object clause conjectures      : 27
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 25
% 0.12/0.37  # Proof object initial formulas used   : 19
% 0.12/0.37  # Proof object generating inferences   : 16
% 0.12/0.37  # Proof object simplifying inferences  : 47
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 19
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 32
% 0.12/0.37  # Removed in clause preprocessing      : 3
% 0.12/0.37  # Initial clauses in saturation        : 29
% 0.12/0.37  # Processed clauses                    : 108
% 0.12/0.37  # ...of these trivial                  : 3
% 0.12/0.37  # ...subsumed                          : 6
% 0.12/0.37  # ...remaining for further processing  : 99
% 0.12/0.37  # Other redundant clauses eliminated   : 4
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 3
% 0.12/0.37  # Backward-rewritten                   : 18
% 0.12/0.37  # Generated clauses                    : 75
% 0.12/0.37  # ...of the previous two non-trivial   : 74
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 71
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
% 0.12/0.37  # Current number of processed clauses  : 47
% 0.12/0.37  #    Positive orientable unit clauses  : 13
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 5
% 0.12/0.37  #    Non-unit-clauses                  : 29
% 0.12/0.37  # Current number of unprocessed clauses: 11
% 0.12/0.37  # ...number of literals in the above   : 37
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 51
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 244
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 88
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 4
% 0.12/0.37  # Unit Clause-clause subsumption calls : 25
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 3
% 0.12/0.37  # BW rewrite match successes           : 3
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 3158
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.032 s
% 0.12/0.37  # System time              : 0.005 s
% 0.12/0.37  # Total time               : 0.036 s
% 0.12/0.37  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
