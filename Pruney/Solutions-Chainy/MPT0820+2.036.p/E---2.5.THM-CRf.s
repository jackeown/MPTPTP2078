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
% DateTime   : Thu Dec  3 10:57:15 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 139 expanded)
%              Number of clauses        :   41 (  63 expanded)
%              Number of leaves         :   16 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  171 ( 272 expanded)
%              Number of equality atoms :   17 (  45 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t19_relset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => r1_tarski(k3_relat_1(X3),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(c_0_16,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X16,X15)
        | r1_tarski(X16,X14)
        | X15 != k1_zfmisc_1(X14) )
      & ( ~ r1_tarski(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k1_zfmisc_1(X14) )
      & ( ~ r2_hidden(esk1_2(X18,X19),X19)
        | ~ r1_tarski(esk1_2(X18,X19),X18)
        | X19 = k1_zfmisc_1(X18) )
      & ( r2_hidden(esk1_2(X18,X19),X19)
        | r1_tarski(esk1_2(X18,X19),X18)
        | X19 = k1_zfmisc_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_17,plain,(
    ! [X27,X28,X29] :
      ( ~ r2_hidden(X27,X28)
      | ~ m1_subset_1(X28,k1_zfmisc_1(X29))
      | m1_subset_1(X27,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => r1_tarski(k3_relat_1(X3),k2_xboole_0(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t19_relset_1])).

fof(c_0_20,plain,(
    ! [X21,X22] : k3_tarski(k2_tarski(X21,X22)) = k2_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X32,X33] :
      ( ( ~ v4_relat_1(X33,X32)
        | r1_tarski(k1_relat_1(X33),X32)
        | ~ v1_relat_1(X33) )
      & ( ~ r1_tarski(k1_relat_1(X33),X32)
        | v4_relat_1(X33,X32)
        | ~ v1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_25,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | v1_relat_1(X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_26,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & ~ r1_tarski(k3_relat_1(esk4_0),k2_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_27,plain,(
    ! [X37,X38] : v1_relat_1(k2_zfmisc_1(X37,X38)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_28,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | ~ r1_tarski(X11,X10)
      | r1_tarski(k2_xboole_0(X9,X11),X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_29,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_31,plain,(
    ! [X36] :
      ( ~ v1_relat_1(X36)
      | k3_relat_1(X36) = k2_xboole_0(k1_relat_1(X36),k2_relat_1(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,X2)
    | ~ m1_subset_1(k1_zfmisc_1(X3),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_33,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_37,plain,(
    ! [X39,X40,X41] :
      ( ( v4_relat_1(X41,X39)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( v5_relat_1(X41,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_38,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( m1_subset_1(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(k1_zfmisc_1(X3),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_43,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk4_0),k2_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_45,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( k3_relat_1(X1) = k3_tarski(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_40,c_0_39])).

fof(c_0_47,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | r1_tarski(X4,k2_xboole_0(X6,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_48,plain,(
    ! [X25,X26] :
      ( ( ~ m1_subset_1(X25,k1_zfmisc_1(X26))
        | r1_tarski(X25,X26) )
      & ( ~ r1_tarski(X25,X26)
        | m1_subset_1(X25,k1_zfmisc_1(X26)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk4_0),X1)
    | ~ v4_relat_1(esk4_0,X2)
    | ~ m1_subset_1(k1_zfmisc_1(X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( v4_relat_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_35])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk4_0),k3_tarski(k1_enumset1(esk2_0,esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_39])).

cnf(c_0_52,plain,
    ( r1_tarski(k3_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk4_0),X1)
    | ~ m1_subset_1(k1_zfmisc_1(esk2_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk4_0),k3_tarski(k1_enumset1(esk2_0,esk2_0,esk3_0)))
    | ~ r1_tarski(k1_relat_1(esk4_0),k3_tarski(k1_enumset1(esk2_0,esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_42])])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X3,X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_53,c_0_39])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),X1)
    | ~ m1_subset_1(k1_zfmisc_1(esk2_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_60,plain,(
    ! [X7,X8] : r1_tarski(X7,k2_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk4_0),k3_tarski(k1_enumset1(esk2_0,esk2_0,esk3_0)))
    | ~ r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),X1)
    | ~ r1_tarski(k1_zfmisc_1(esk2_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

fof(c_0_63,plain,(
    ! [X23,X24] :
      ( ~ r1_tarski(X23,X24)
      | r1_tarski(k1_zfmisc_1(X23),k1_zfmisc_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_tarski(k1_zfmisc_1(esk2_0),k1_zfmisc_1(k3_tarski(k1_enumset1(esk2_0,esk2_0,esk3_0))))
    | ~ r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_64,c_0_39])).

fof(c_0_68,plain,(
    ! [X34,X35] :
      ( ( ~ v5_relat_1(X35,X34)
        | r1_tarski(k2_relat_1(X35),X34)
        | ~ v1_relat_1(X35) )
      & ( ~ r1_tarski(k2_relat_1(X35),X34)
        | v5_relat_1(X35,X34)
        | ~ v1_relat_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_69,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_70,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_71,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( v5_relat_1(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_35])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:01:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05BN
% 0.20/0.39  # and selection function SelectUnlessUniqMaxSmallestOrientable.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.027 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.39  fof(t19_relset_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>r1_tarski(k3_relat_1(X3),k2_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relset_1)).
% 0.20/0.39  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.39  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.20/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.39  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.20/0.39  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 0.20/0.39  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.39  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.20/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.39  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.39  fof(t79_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 0.20/0.39  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.20/0.39  fof(c_0_16, plain, ![X14, X15, X16, X17, X18, X19]:(((~r2_hidden(X16,X15)|r1_tarski(X16,X14)|X15!=k1_zfmisc_1(X14))&(~r1_tarski(X17,X14)|r2_hidden(X17,X15)|X15!=k1_zfmisc_1(X14)))&((~r2_hidden(esk1_2(X18,X19),X19)|~r1_tarski(esk1_2(X18,X19),X18)|X19=k1_zfmisc_1(X18))&(r2_hidden(esk1_2(X18,X19),X19)|r1_tarski(esk1_2(X18,X19),X18)|X19=k1_zfmisc_1(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.39  fof(c_0_17, plain, ![X27, X28, X29]:(~r2_hidden(X27,X28)|~m1_subset_1(X28,k1_zfmisc_1(X29))|m1_subset_1(X27,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.39  cnf(c_0_18, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>r1_tarski(k3_relat_1(X3),k2_xboole_0(X1,X2)))), inference(assume_negation,[status(cth)],[t19_relset_1])).
% 0.20/0.39  fof(c_0_20, plain, ![X21, X22]:k3_tarski(k2_tarski(X21,X22))=k2_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.39  fof(c_0_21, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.39  cnf(c_0_22, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_23, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_18])).
% 0.20/0.39  fof(c_0_24, plain, ![X32, X33]:((~v4_relat_1(X33,X32)|r1_tarski(k1_relat_1(X33),X32)|~v1_relat_1(X33))&(~r1_tarski(k1_relat_1(X33),X32)|v4_relat_1(X33,X32)|~v1_relat_1(X33))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.20/0.39  fof(c_0_25, plain, ![X30, X31]:(~v1_relat_1(X30)|(~m1_subset_1(X31,k1_zfmisc_1(X30))|v1_relat_1(X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.39  fof(c_0_26, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))&~r1_tarski(k3_relat_1(esk4_0),k2_xboole_0(esk2_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.20/0.39  fof(c_0_27, plain, ![X37, X38]:v1_relat_1(k2_zfmisc_1(X37,X38)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.39  fof(c_0_28, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|~r1_tarski(X11,X10)|r1_tarski(k2_xboole_0(X9,X11),X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.20/0.39  cnf(c_0_29, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  fof(c_0_31, plain, ![X36]:(~v1_relat_1(X36)|k3_relat_1(X36)=k2_xboole_0(k1_relat_1(X36),k2_relat_1(X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.20/0.39  cnf(c_0_32, plain, (m1_subset_1(X1,X2)|~m1_subset_1(k1_zfmisc_1(X3),k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.39  cnf(c_0_33, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_34, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_36, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  fof(c_0_37, plain, ![X39, X40, X41]:((v4_relat_1(X41,X39)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(v5_relat_1(X41,X40)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.39  cnf(c_0_38, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  cnf(c_0_39, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.39  cnf(c_0_40, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.39  cnf(c_0_41, plain, (m1_subset_1(k1_relat_1(X1),X2)|~v4_relat_1(X1,X3)|~v1_relat_1(X1)|~m1_subset_1(k1_zfmisc_1(X3),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.39  cnf(c_0_42, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.20/0.39  cnf(c_0_43, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.39  cnf(c_0_44, negated_conjecture, (~r1_tarski(k3_relat_1(esk4_0),k2_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_45, plain, (r1_tarski(k3_tarski(k1_enumset1(X1,X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.39  cnf(c_0_46, plain, (k3_relat_1(X1)=k3_tarski(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_40, c_0_39])).
% 0.20/0.39  fof(c_0_47, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|r1_tarski(X4,k2_xboole_0(X6,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.20/0.39  fof(c_0_48, plain, ![X25, X26]:((~m1_subset_1(X25,k1_zfmisc_1(X26))|r1_tarski(X25,X26))&(~r1_tarski(X25,X26)|m1_subset_1(X25,k1_zfmisc_1(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (m1_subset_1(k1_relat_1(esk4_0),X1)|~v4_relat_1(esk4_0,X2)|~m1_subset_1(k1_zfmisc_1(X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.39  cnf(c_0_50, negated_conjecture, (v4_relat_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_43, c_0_35])).
% 0.20/0.39  cnf(c_0_51, negated_conjecture, (~r1_tarski(k3_relat_1(esk4_0),k3_tarski(k1_enumset1(esk2_0,esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_44, c_0_39])).
% 0.20/0.39  cnf(c_0_52, plain, (r1_tarski(k3_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.39  cnf(c_0_53, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.39  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.39  cnf(c_0_55, negated_conjecture, (m1_subset_1(k1_relat_1(esk4_0),X1)|~m1_subset_1(k1_zfmisc_1(esk2_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.39  cnf(c_0_56, negated_conjecture, (~r1_tarski(k2_relat_1(esk4_0),k3_tarski(k1_enumset1(esk2_0,esk2_0,esk3_0)))|~r1_tarski(k1_relat_1(esk4_0),k3_tarski(k1_enumset1(esk2_0,esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_42])])).
% 0.20/0.39  cnf(c_0_57, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X3,X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_53, c_0_39])).
% 0.20/0.39  cnf(c_0_58, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),X1)|~m1_subset_1(k1_zfmisc_1(esk2_0),k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.39  cnf(c_0_59, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.39  fof(c_0_60, plain, ![X7, X8]:r1_tarski(X7,k2_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.39  cnf(c_0_61, negated_conjecture, (~r1_tarski(k1_relat_1(esk4_0),k3_tarski(k1_enumset1(esk2_0,esk2_0,esk3_0)))|~r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.39  cnf(c_0_62, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),X1)|~r1_tarski(k1_zfmisc_1(esk2_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.39  fof(c_0_63, plain, ![X23, X24]:(~r1_tarski(X23,X24)|r1_tarski(k1_zfmisc_1(X23),k1_zfmisc_1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).
% 0.20/0.39  cnf(c_0_64, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.39  cnf(c_0_65, negated_conjecture, (~r1_tarski(k1_zfmisc_1(esk2_0),k1_zfmisc_1(k3_tarski(k1_enumset1(esk2_0,esk2_0,esk3_0))))|~r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.39  cnf(c_0_66, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.39  cnf(c_0_67, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_64, c_0_39])).
% 0.20/0.39  fof(c_0_68, plain, ![X34, X35]:((~v5_relat_1(X35,X34)|r1_tarski(k2_relat_1(X35),X34)|~v1_relat_1(X35))&(~r1_tarski(k2_relat_1(X35),X34)|v5_relat_1(X35,X34)|~v1_relat_1(X35))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.20/0.39  cnf(c_0_69, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.39  cnf(c_0_70, negated_conjecture, (~r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])])).
% 0.20/0.39  cnf(c_0_71, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.39  cnf(c_0_72, negated_conjecture, (v5_relat_1(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_69, c_0_35])).
% 0.20/0.39  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), c_0_42])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 74
% 0.20/0.39  # Proof object clause steps            : 41
% 0.20/0.39  # Proof object formula steps           : 33
% 0.20/0.39  # Proof object conjectures             : 18
% 0.20/0.39  # Proof object clause conjectures      : 15
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 19
% 0.20/0.39  # Proof object initial formulas used   : 16
% 0.20/0.39  # Proof object generating inferences   : 15
% 0.20/0.39  # Proof object simplifying inferences  : 16
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 16
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 24
% 0.20/0.39  # Removed in clause preprocessing      : 2
% 0.20/0.39  # Initial clauses in saturation        : 22
% 0.20/0.39  # Processed clauses                    : 253
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 31
% 0.20/0.39  # ...remaining for further processing  : 222
% 0.20/0.39  # Other redundant clauses eliminated   : 2
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 0
% 0.20/0.39  # Generated clauses                    : 767
% 0.20/0.39  # ...of the previous two non-trivial   : 748
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 763
% 0.20/0.39  # Factorizations                       : 2
% 0.20/0.39  # Equation resolutions                 : 2
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 198
% 0.20/0.39  #    Positive orientable unit clauses  : 14
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 7
% 0.20/0.39  #    Non-unit-clauses                  : 177
% 0.20/0.39  # Current number of unprocessed clauses: 539
% 0.20/0.39  # ...number of literals in the above   : 2014
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 24
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 4179
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 3613
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 25
% 0.20/0.39  # Unit Clause-clause subsumption calls : 269
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 2
% 0.20/0.39  # BW rewrite match successes           : 0
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 15031
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.051 s
% 0.20/0.39  # System time              : 0.005 s
% 0.20/0.39  # Total time               : 0.056 s
% 0.20/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
