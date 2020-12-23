%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:32 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 489 expanded)
%              Number of clauses        :   54 ( 194 expanded)
%              Number of leaves         :   22 ( 139 expanded)
%              Depth                    :   12
%              Number of atoms          :  257 ( 944 expanded)
%              Number of equality atoms :  102 ( 501 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(t14_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t39_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
     => ( k7_relset_1(X2,X1,X3,k8_relset_1(X2,X1,X3,X1)) = k2_relset_1(X2,X1,X3)
        & k8_relset_1(X2,X1,X3,k7_relset_1(X2,X1,X3,X2)) = k1_relset_1(X2,X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

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

fof(c_0_22,plain,(
    ! [X28,X29,X30] :
      ( ~ r2_hidden(X28,X29)
      | ~ m1_subset_1(X29,k1_zfmisc_1(X30))
      | ~ v1_xboole_0(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_23,plain,(
    ! [X22] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X22)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_24,plain,(
    ! [X11] :
      ( ~ v1_xboole_0(X11)
      | X11 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_30,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => k2_relset_1(k1_tarski(X1),X2,X3) = k1_tarski(k1_funct_1(X3,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t62_funct_2])).

cnf(c_0_31,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_34,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,k1_tarski(esk2_0),esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0)))
    & esk3_0 != k1_xboole_0
    & k2_relset_1(k1_tarski(esk2_0),esk3_0,esk4_0) != k1_tarski(k1_funct_1(esk4_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).

fof(c_0_35,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_36,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_37,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_38,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_33])).

fof(c_0_41,plain,(
    ! [X42,X43,X44,X45] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | m1_subset_1(k8_relset_1(X42,X43,X44,X45),k1_zfmisc_1(X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).

fof(c_0_42,plain,(
    ! [X49,X50,X51,X52] :
      ( ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
      | k8_relset_1(X49,X50,X51,X52) = k10_relat_1(X51,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_43,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X35)
      | ~ v1_funct_1(X35)
      | k1_relat_1(X35) != k1_tarski(X34)
      | k2_relat_1(X35) = k1_tarski(k1_funct_1(X35,X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).

fof(c_0_44,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | v1_relat_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_51,plain,(
    ! [X23,X24] :
      ( ( ~ m1_subset_1(X23,k1_zfmisc_1(X24))
        | r1_tarski(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | m1_subset_1(X23,k1_zfmisc_1(X24)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_52,plain,
    ( m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_54,plain,(
    ! [X20,X21] :
      ( ( ~ r1_tarski(X20,k1_tarski(X21))
        | X20 = k1_xboole_0
        | X20 = k1_tarski(X21) )
      & ( X20 != k1_xboole_0
        | r1_tarski(X20,k1_tarski(X21)) )
      & ( X20 != k1_tarski(X21)
        | r1_tarski(X20,k1_tarski(X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_55,negated_conjecture,
    ( k2_relset_1(k1_tarski(esk2_0),esk3_0,esk4_0) != k1_tarski(k1_funct_1(esk4_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_56,plain,
    ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X1) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,plain,
    ( m1_subset_1(k10_relat_1(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_63,plain,(
    ! [X31,X32] :
      ( ( ~ v4_relat_1(X32,X31)
        | r1_tarski(k1_relat_1(X32),X31)
        | ~ v1_relat_1(X32) )
      & ( ~ r1_tarski(k1_relat_1(X32),X31)
        | v4_relat_1(X32,X31)
        | ~ v1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_64,plain,(
    ! [X39,X40,X41] :
      ( ( v4_relat_1(X41,X39)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( v5_relat_1(X41,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_65,negated_conjecture,
    ( k2_relset_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk4_0) != k2_enumset1(k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48])).

cnf(c_0_66,plain,
    ( k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))
    | k1_relat_1(X1) != k2_enumset1(X2,X2,X2,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_68,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

fof(c_0_69,plain,(
    ! [X46,X47,X48] :
      ( ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
      | k2_relset_1(X46,X47,X48) = k2_relat_1(X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_70,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_71,plain,
    ( m1_subset_1(k10_relat_1(k1_xboole_0,X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_26])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | ~ r1_tarski(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_48])).

cnf(c_0_73,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_74,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_75,negated_conjecture,
    ( k2_relset_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk4_0) != k2_relat_1(esk4_0)
    | k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0) != k1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_68])])).

cnf(c_0_76,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_77,plain,
    ( k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

fof(c_0_78,plain,(
    ! [X53,X54,X55] :
      ( ( k7_relset_1(X54,X53,X55,k8_relset_1(X54,X53,X55,X53)) = k2_relset_1(X54,X53,X55)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X54,X53))) )
      & ( k8_relset_1(X54,X53,X55,k7_relset_1(X54,X53,X55,X54)) = k1_relset_1(X54,X53,X55)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X54,X53))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_relset_1])])])).

fof(c_0_79,plain,(
    ! [X33] :
      ( ( k1_relat_1(X33) != k1_xboole_0
        | X33 = k1_xboole_0
        | ~ v1_relat_1(X33) )
      & ( k2_relat_1(X33) != k1_xboole_0
        | X33 = k1_xboole_0
        | ~ v1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_80,plain,
    ( k1_relat_1(X1) = k2_enumset1(X2,X2,X2,X2)
    | k1_relat_1(X1) = k1_xboole_0
    | ~ v4_relat_1(X1,k2_enumset1(X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( v4_relat_1(esk4_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_58])).

cnf(c_0_82,negated_conjecture,
    ( k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0) != k1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_58])])).

fof(c_0_83,plain,(
    ! [X56,X57,X58] :
      ( ( ~ v1_funct_2(X58,X56,X57)
        | X56 = k1_relset_1(X56,X57,X58)
        | X57 = k1_xboole_0
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( X56 != k1_relset_1(X56,X57,X58)
        | v1_funct_2(X58,X56,X57)
        | X57 = k1_xboole_0
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( ~ v1_funct_2(X58,X56,X57)
        | X56 = k1_relset_1(X56,X57,X58)
        | X56 != k1_xboole_0
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( X56 != k1_relset_1(X56,X57,X58)
        | v1_funct_2(X58,X56,X57)
        | X56 != k1_xboole_0
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( ~ v1_funct_2(X58,X56,X57)
        | X58 = k1_xboole_0
        | X56 = k1_xboole_0
        | X57 != k1_xboole_0
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( X58 != k1_xboole_0
        | v1_funct_2(X58,X56,X57)
        | X56 = k1_xboole_0
        | X57 != k1_xboole_0
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_84,plain,
    ( k8_relset_1(X1,X2,k1_xboole_0,X3) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_77]),c_0_26])])).

cnf(c_0_85,plain,
    ( k8_relset_1(X1,X2,X3,k7_relset_1(X1,X2,X3,X1)) = k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_tarski(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_87,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_88,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_68])]),c_0_82])).

cnf(c_0_89,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_90,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_26])])).

cnf(c_0_91,negated_conjecture,
    ( v1_funct_2(esk4_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_92,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_68])])).

cnf(c_0_93,plain,
    ( X1 = k1_xboole_0
    | k1_xboole_0 = X2
    | ~ v1_funct_2(k1_xboole_0,X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_26])])).

cnf(c_0_94,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_96,negated_conjecture,
    ( k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_82,c_0_88])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95]),c_0_96]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.37/0.53  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.37/0.53  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.37/0.53  #
% 0.37/0.53  # Preprocessing time       : 0.029 s
% 0.37/0.53  
% 0.37/0.53  # Proof found!
% 0.37/0.53  # SZS status Theorem
% 0.37/0.53  # SZS output start CNFRefutation
% 0.37/0.53  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.37/0.53  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.37/0.53  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.37/0.53  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.37/0.53  fof(dt_o_0_0_xboole_0, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 0.37/0.53  fof(t62_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>k2_relset_1(k1_tarski(X1),X2,X3)=k1_tarski(k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 0.37/0.53  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.37/0.53  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.37/0.53  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.37/0.53  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.37/0.53  fof(dt_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 0.37/0.53  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.37/0.53  fof(t14_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 0.37/0.53  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.37/0.53  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.37/0.53  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.37/0.53  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.37/0.53  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.37/0.53  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.37/0.53  fof(t39_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(k7_relset_1(X2,X1,X3,k8_relset_1(X2,X1,X3,X1))=k2_relset_1(X2,X1,X3)&k8_relset_1(X2,X1,X3,k7_relset_1(X2,X1,X3,X2))=k1_relset_1(X2,X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 0.37/0.53  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.37/0.53  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.37/0.53  fof(c_0_22, plain, ![X28, X29, X30]:(~r2_hidden(X28,X29)|~m1_subset_1(X29,k1_zfmisc_1(X30))|~v1_xboole_0(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.37/0.53  fof(c_0_23, plain, ![X22]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X22)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.37/0.53  fof(c_0_24, plain, ![X11]:(~v1_xboole_0(X11)|X11=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.37/0.53  cnf(c_0_25, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.37/0.53  cnf(c_0_26, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.37/0.53  fof(c_0_27, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.37/0.53  cnf(c_0_28, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.37/0.53  cnf(c_0_29, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).
% 0.37/0.53  fof(c_0_30, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>k2_relset_1(k1_tarski(X1),X2,X3)=k1_tarski(k1_funct_1(X3,X1))))), inference(assume_negation,[status(cth)],[t62_funct_2])).
% 0.37/0.53  cnf(c_0_31, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.37/0.53  cnf(c_0_32, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.37/0.53  cnf(c_0_33, plain, (o_0_0_xboole_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.37/0.53  fof(c_0_34, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,k1_tarski(esk2_0),esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))))&(esk3_0!=k1_xboole_0&k2_relset_1(k1_tarski(esk2_0),esk3_0,esk4_0)!=k1_tarski(k1_funct_1(esk4_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).
% 0.37/0.53  fof(c_0_35, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.37/0.53  fof(c_0_36, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.37/0.53  fof(c_0_37, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.37/0.53  fof(c_0_38, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.37/0.53  cnf(c_0_39, plain, (r1_tarski(k1_xboole_0,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.37/0.53  cnf(c_0_40, plain, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_29, c_0_33])).
% 0.37/0.53  fof(c_0_41, plain, ![X42, X43, X44, X45]:(~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|m1_subset_1(k8_relset_1(X42,X43,X44,X45),k1_zfmisc_1(X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).
% 0.37/0.53  fof(c_0_42, plain, ![X49, X50, X51, X52]:(~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|k8_relset_1(X49,X50,X51,X52)=k10_relat_1(X51,X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.37/0.53  fof(c_0_43, plain, ![X34, X35]:(~v1_relat_1(X35)|~v1_funct_1(X35)|(k1_relat_1(X35)!=k1_tarski(X34)|k2_relat_1(X35)=k1_tarski(k1_funct_1(X35,X34)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).
% 0.37/0.53  fof(c_0_44, plain, ![X36, X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|v1_relat_1(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.37/0.53  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.37/0.53  cnf(c_0_46, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.37/0.53  cnf(c_0_47, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.37/0.53  cnf(c_0_48, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.37/0.53  cnf(c_0_49, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.37/0.53  cnf(c_0_50, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.37/0.53  fof(c_0_51, plain, ![X23, X24]:((~m1_subset_1(X23,k1_zfmisc_1(X24))|r1_tarski(X23,X24))&(~r1_tarski(X23,X24)|m1_subset_1(X23,k1_zfmisc_1(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.37/0.53  cnf(c_0_52, plain, (m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.37/0.53  cnf(c_0_53, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.37/0.53  fof(c_0_54, plain, ![X20, X21]:((~r1_tarski(X20,k1_tarski(X21))|(X20=k1_xboole_0|X20=k1_tarski(X21)))&((X20!=k1_xboole_0|r1_tarski(X20,k1_tarski(X21)))&(X20!=k1_tarski(X21)|r1_tarski(X20,k1_tarski(X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.37/0.53  cnf(c_0_55, negated_conjecture, (k2_relset_1(k1_tarski(esk2_0),esk3_0,esk4_0)!=k1_tarski(k1_funct_1(esk4_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.37/0.53  cnf(c_0_56, plain, (k2_relat_1(X1)=k1_tarski(k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|k1_relat_1(X1)!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.37/0.53  cnf(c_0_57, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.37/0.53  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48])).
% 0.37/0.53  cnf(c_0_59, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.37/0.53  cnf(c_0_60, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.37/0.53  cnf(c_0_61, plain, (m1_subset_1(k10_relat_1(X1,X2),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.37/0.53  cnf(c_0_62, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.37/0.53  fof(c_0_63, plain, ![X31, X32]:((~v4_relat_1(X32,X31)|r1_tarski(k1_relat_1(X32),X31)|~v1_relat_1(X32))&(~r1_tarski(k1_relat_1(X32),X31)|v4_relat_1(X32,X31)|~v1_relat_1(X32))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.37/0.53  fof(c_0_64, plain, ![X39, X40, X41]:((v4_relat_1(X41,X39)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(v5_relat_1(X41,X40)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.37/0.53  cnf(c_0_65, negated_conjecture, (k2_relset_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk4_0)!=k2_enumset1(k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0),k1_funct_1(esk4_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48])).
% 0.37/0.53  cnf(c_0_66, plain, (k2_relat_1(X1)=k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))|k1_relat_1(X1)!=k2_enumset1(X2,X2,X2,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48])).
% 0.37/0.53  cnf(c_0_67, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.37/0.53  cnf(c_0_68, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.37/0.53  fof(c_0_69, plain, ![X46, X47, X48]:(~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))|k2_relset_1(X46,X47,X48)=k2_relat_1(X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.37/0.53  cnf(c_0_70, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.37/0.53  cnf(c_0_71, plain, (m1_subset_1(k10_relat_1(k1_xboole_0,X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_61, c_0_26])).
% 0.37/0.53  cnf(c_0_72, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|~r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_48])).
% 0.37/0.53  cnf(c_0_73, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.37/0.53  cnf(c_0_74, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.37/0.53  cnf(c_0_75, negated_conjecture, (k2_relset_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk4_0)!=k2_relat_1(esk4_0)|k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)!=k1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_68])])).
% 0.37/0.53  cnf(c_0_76, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.37/0.53  cnf(c_0_77, plain, (k10_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.37/0.53  fof(c_0_78, plain, ![X53, X54, X55]:((k7_relset_1(X54,X53,X55,k8_relset_1(X54,X53,X55,X53))=k2_relset_1(X54,X53,X55)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X54,X53))))&(k8_relset_1(X54,X53,X55,k7_relset_1(X54,X53,X55,X54))=k1_relset_1(X54,X53,X55)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X54,X53))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_relset_1])])])).
% 0.37/0.53  fof(c_0_79, plain, ![X33]:((k1_relat_1(X33)!=k1_xboole_0|X33=k1_xboole_0|~v1_relat_1(X33))&(k2_relat_1(X33)!=k1_xboole_0|X33=k1_xboole_0|~v1_relat_1(X33))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.37/0.53  cnf(c_0_80, plain, (k1_relat_1(X1)=k2_enumset1(X2,X2,X2,X2)|k1_relat_1(X1)=k1_xboole_0|~v4_relat_1(X1,k2_enumset1(X2,X2,X2,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.37/0.53  cnf(c_0_81, negated_conjecture, (v4_relat_1(esk4_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_74, c_0_58])).
% 0.37/0.53  cnf(c_0_82, negated_conjecture, (k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)!=k1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_58])])).
% 0.37/0.53  fof(c_0_83, plain, ![X56, X57, X58]:((((~v1_funct_2(X58,X56,X57)|X56=k1_relset_1(X56,X57,X58)|X57=k1_xboole_0|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))&(X56!=k1_relset_1(X56,X57,X58)|v1_funct_2(X58,X56,X57)|X57=k1_xboole_0|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))))&((~v1_funct_2(X58,X56,X57)|X56=k1_relset_1(X56,X57,X58)|X56!=k1_xboole_0|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))&(X56!=k1_relset_1(X56,X57,X58)|v1_funct_2(X58,X56,X57)|X56!=k1_xboole_0|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))))&((~v1_funct_2(X58,X56,X57)|X58=k1_xboole_0|X56=k1_xboole_0|X57!=k1_xboole_0|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))&(X58!=k1_xboole_0|v1_funct_2(X58,X56,X57)|X56=k1_xboole_0|X57!=k1_xboole_0|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.37/0.53  cnf(c_0_84, plain, (k8_relset_1(X1,X2,k1_xboole_0,X3)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_77]), c_0_26])])).
% 0.37/0.53  cnf(c_0_85, plain, (k8_relset_1(X1,X2,X3,k7_relset_1(X1,X2,X3,X1))=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.37/0.53  cnf(c_0_86, negated_conjecture, (v1_funct_2(esk4_0,k1_tarski(esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.37/0.53  cnf(c_0_87, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.37/0.53  cnf(c_0_88, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_68])]), c_0_82])).
% 0.37/0.53  cnf(c_0_89, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.37/0.53  cnf(c_0_90, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_26])])).
% 0.37/0.53  cnf(c_0_91, negated_conjecture, (v1_funct_2(esk4_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_46]), c_0_47]), c_0_48])).
% 0.37/0.53  cnf(c_0_92, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_68])])).
% 0.37/0.53  cnf(c_0_93, plain, (X1=k1_xboole_0|k1_xboole_0=X2|~v1_funct_2(k1_xboole_0,X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_26])])).
% 0.37/0.53  cnf(c_0_94, negated_conjecture, (v1_funct_2(k1_xboole_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)), inference(rw,[status(thm)],[c_0_91, c_0_92])).
% 0.37/0.53  cnf(c_0_95, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.37/0.53  cnf(c_0_96, negated_conjecture, (k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_82, c_0_88])).
% 0.37/0.53  cnf(c_0_97, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95]), c_0_96]), ['proof']).
% 0.37/0.53  # SZS output end CNFRefutation
% 0.37/0.53  # Proof object total steps             : 98
% 0.37/0.53  # Proof object clause steps            : 54
% 0.37/0.53  # Proof object formula steps           : 44
% 0.37/0.53  # Proof object conjectures             : 20
% 0.37/0.53  # Proof object clause conjectures      : 17
% 0.37/0.53  # Proof object formula conjectures     : 3
% 0.37/0.53  # Proof object initial clauses used    : 26
% 0.37/0.53  # Proof object initial formulas used   : 22
% 0.37/0.53  # Proof object generating inferences   : 20
% 0.37/0.53  # Proof object simplifying inferences  : 45
% 0.37/0.53  # Training examples: 0 positive, 0 negative
% 0.37/0.53  # Parsed axioms                        : 23
% 0.37/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.37/0.53  # Initial clauses                      : 43
% 0.37/0.53  # Removed in clause preprocessing      : 3
% 0.37/0.53  # Initial clauses in saturation        : 40
% 0.37/0.53  # Processed clauses                    : 1914
% 0.37/0.53  # ...of these trivial                  : 1
% 0.37/0.53  # ...subsumed                          : 1321
% 0.37/0.53  # ...remaining for further processing  : 592
% 0.37/0.53  # Other redundant clauses eliminated   : 10
% 0.37/0.53  # Clauses deleted for lack of memory   : 0
% 0.37/0.53  # Backward-subsumed                    : 17
% 0.37/0.53  # Backward-rewritten                   : 47
% 0.37/0.53  # Generated clauses                    : 9197
% 0.37/0.53  # ...of the previous two non-trivial   : 6865
% 0.37/0.53  # Contextual simplify-reflections      : 29
% 0.37/0.53  # Paramodulations                      : 9188
% 0.37/0.53  # Factorizations                       : 0
% 0.37/0.53  # Equation resolutions                 : 10
% 0.37/0.53  # Propositional unsat checks           : 0
% 0.37/0.53  #    Propositional check models        : 0
% 0.37/0.53  #    Propositional check unsatisfiable : 0
% 0.37/0.53  #    Propositional clauses             : 0
% 0.37/0.53  #    Propositional clauses after purity: 0
% 0.37/0.53  #    Propositional unsat core size     : 0
% 0.37/0.53  #    Propositional preprocessing time  : 0.000
% 0.37/0.53  #    Propositional encoding time       : 0.000
% 0.37/0.53  #    Propositional solver time         : 0.000
% 0.37/0.53  #    Success case prop preproc time    : 0.000
% 0.37/0.53  #    Success case prop encoding time   : 0.000
% 0.37/0.53  #    Success case prop solver time     : 0.000
% 0.37/0.53  # Current number of processed clauses  : 520
% 0.37/0.53  #    Positive orientable unit clauses  : 71
% 0.37/0.53  #    Positive unorientable unit clauses: 0
% 0.37/0.53  #    Negative unit clauses             : 5
% 0.37/0.53  #    Non-unit-clauses                  : 444
% 0.37/0.53  # Current number of unprocessed clauses: 4966
% 0.37/0.53  # ...number of literals in the above   : 16958
% 0.37/0.53  # Current number of archived formulas  : 0
% 0.37/0.53  # Current number of archived clauses   : 67
% 0.37/0.53  # Clause-clause subsumption calls (NU) : 27077
% 0.37/0.53  # Rec. Clause-clause subsumption calls : 20481
% 0.37/0.53  # Non-unit clause-clause subsumptions  : 1018
% 0.37/0.53  # Unit Clause-clause subsumption calls : 1230
% 0.37/0.53  # Rewrite failures with RHS unbound    : 0
% 0.37/0.53  # BW rewrite match attempts            : 215
% 0.37/0.53  # BW rewrite match successes           : 6
% 0.37/0.53  # Condensation attempts                : 0
% 0.37/0.53  # Condensation successes               : 0
% 0.37/0.53  # Termbank termtop insertions          : 126247
% 0.37/0.53  
% 0.37/0.53  # -------------------------------------------------
% 0.37/0.53  # User time                : 0.174 s
% 0.37/0.53  # System time              : 0.008 s
% 0.37/0.53  # Total time               : 0.182 s
% 0.37/0.53  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
