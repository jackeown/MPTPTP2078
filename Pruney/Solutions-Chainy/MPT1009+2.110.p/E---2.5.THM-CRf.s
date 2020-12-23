%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:03 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  108 (2280 expanded)
%              Number of clauses        :   65 ( 972 expanded)
%              Number of leaves         :   21 ( 613 expanded)
%              Depth                    :   15
%              Number of atoms          :  271 (4759 expanded)
%              Number of equality atoms :   92 (1851 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,k1_tarski(X1),X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(t118_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k1_relat_1(X3)) )
       => k9_relat_1(X3,k2_tarski(X1,X2)) = k2_tarski(k1_funct_1(X3,X1),k1_funct_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(t144_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,k1_tarski(X1),X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t64_funct_2])).

fof(c_0_22,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(X32))
      | v1_relat_1(X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_23,plain,(
    ! [X38,X39] : v1_relat_1(k2_zfmisc_1(X38,X39)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_24,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,k1_tarski(esk2_0),esk3_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0)))
    & esk3_0 != k1_xboole_0
    & ~ r1_tarski(k7_relset_1(k1_tarski(esk2_0),esk3_0,esk5_0,esk4_0),k1_tarski(k1_funct_1(esk5_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_25,plain,(
    ! [X16] : k2_tarski(X16,X16) = k1_tarski(X16) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_26,plain,(
    ! [X17,X18] : k1_enumset1(X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,plain,(
    ! [X19,X20,X21] : k2_enumset1(X19,X19,X20,X21) = k1_enumset1(X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_28,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X34,X35] :
      ( ( ~ v4_relat_1(X35,X34)
        | r1_tarski(k1_relat_1(X35),X34)
        | ~ v1_relat_1(X35) )
      & ( ~ r1_tarski(k1_relat_1(X35),X34)
        | v4_relat_1(X35,X34)
        | ~ v1_relat_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_35,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])).

fof(c_0_37,plain,(
    ! [X49,X50,X51] :
      ( ( v4_relat_1(X51,X49)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( v5_relat_1(X51,X50)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_38,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X10,X9)
        | X10 = X7
        | X10 = X8
        | X9 != k2_tarski(X7,X8) )
      & ( X11 != X7
        | r2_hidden(X11,X9)
        | X9 != k2_tarski(X7,X8) )
      & ( X11 != X8
        | r2_hidden(X11,X9)
        | X9 != k2_tarski(X7,X8) )
      & ( esk1_3(X12,X13,X14) != X12
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_tarski(X12,X13) )
      & ( esk1_3(X12,X13,X14) != X13
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_tarski(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X14)
        | esk1_3(X12,X13,X14) = X12
        | esk1_3(X12,X13,X14) = X13
        | X14 = k2_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_39,plain,(
    ! [X22,X23] :
      ( ( ~ r1_tarski(X22,k1_tarski(X23))
        | X22 = k1_xboole_0
        | X22 = k1_tarski(X23) )
      & ( X22 != k1_xboole_0
        | r1_tarski(X22,k1_tarski(X23)) )
      & ( X22 != k1_tarski(X23)
        | r1_tarski(X22,k1_tarski(X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_43,plain,(
    ! [X56] :
      ( ( v1_funct_1(X56)
        | ~ v1_relat_1(X56)
        | ~ v1_funct_1(X56) )
      & ( v1_funct_2(X56,k1_relat_1(X56),k2_relat_1(X56))
        | ~ v1_relat_1(X56)
        | ~ v1_funct_1(X56) )
      & ( m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X56),k2_relat_1(X56))))
        | ~ v1_relat_1(X56)
        | ~ v1_funct_1(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk5_0),X1)
    | ~ v4_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( v4_relat_1(esk5_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_36])).

fof(c_0_48,plain,(
    ! [X46,X47,X48] :
      ( ~ v1_relat_1(X48)
      | ~ v1_funct_1(X48)
      | ~ r2_hidden(X46,k1_relat_1(X48))
      | ~ r2_hidden(X47,k1_relat_1(X48))
      | k9_relat_1(X48,k2_tarski(X46,X47)) = k2_tarski(k1_funct_1(X48,X46),k1_funct_1(X48,X47)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_funct_1])])).

fof(c_0_49,plain,(
    ! [X27,X28] :
      ( ( ~ m1_subset_1(X27,k1_zfmisc_1(X28))
        | r1_tarski(X27,X28) )
      & ( ~ r1_tarski(X27,X28)
        | m1_subset_1(X27,k1_zfmisc_1(X28)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_32]),c_0_33])).

cnf(c_0_53,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | ~ r1_tarski(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk5_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_55,plain,(
    ! [X24,X25] :
      ( ( k2_zfmisc_1(X24,X25) != k1_xboole_0
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0 )
      & ( X24 != k1_xboole_0
        | k2_zfmisc_1(X24,X25) = k1_xboole_0 )
      & ( X25 != k1_xboole_0
        | k2_zfmisc_1(X24,X25) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_56,plain,(
    ! [X44,X45] :
      ( ~ v1_relat_1(X45)
      | ~ v4_relat_1(X45,X44)
      | X45 = k7_relat_1(X45,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_57,plain,
    ( k9_relat_1(X1,k2_tarski(X2,X3)) = k2_tarski(k1_funct_1(X1,X2),k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),k2_relat_1(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_41]),c_0_51])])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_52])])).

cnf(c_0_61,negated_conjecture,
    ( k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0) = k1_relat_1(esk5_0)
    | k1_relat_1(esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_63,plain,(
    ! [X42,X43] :
      ( ~ v1_relat_1(X43)
      | k2_relat_1(k7_relat_1(X43,X42)) = k9_relat_1(X43,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_64,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_65,plain,(
    ! [X26] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X26)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_66,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_67,plain,(
    ! [X52,X53,X54,X55] :
      ( ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
      | k7_relset_1(X52,X53,X54,X55) = k9_relat_1(X54,X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_68,plain,
    ( k9_relat_1(X1,k2_enumset1(X2,X2,X2,X3)) = k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(k1_relat_1(esk5_0),k2_relat_1(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | r2_hidden(esk2_0,k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_71,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_72,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( k7_relat_1(esk5_0,X1) = esk5_0
    | ~ v4_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_41])).

fof(c_0_74,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_75,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_76,plain,(
    ! [X36,X37] :
      ( ( ~ v5_relat_1(X37,X36)
        | r1_tarski(k2_relat_1(X37),X36)
        | ~ v1_relat_1(X37) )
      & ( ~ r1_tarski(k2_relat_1(X37),X36)
        | v5_relat_1(X37,X36)
        | ~ v1_relat_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_77,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_66])).

cnf(c_0_78,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(esk2_0),esk3_0,esk5_0,esk4_0),k1_tarski(k1_funct_1(esk5_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_80,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_81,negated_conjecture,
    ( k2_enumset1(k1_funct_1(esk5_0,X1),k1_funct_1(esk5_0,X1),k1_funct_1(esk5_0,X1),k1_funct_1(esk5_0,X2)) = k9_relat_1(esk5_0,k2_enumset1(X1,X1,X1,X2))
    | ~ r2_hidden(X2,k1_relat_1(esk5_0))
    | ~ r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_41]),c_0_51])])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk2_0,k1_relat_1(esk5_0))
    | r1_tarski(esk5_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_83,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk5_0,X1)) = k9_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_41])).

cnf(c_0_84,negated_conjecture,
    ( k7_relat_1(esk5_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_47])).

fof(c_0_85,plain,(
    ! [X40,X41] :
      ( ~ v1_relat_1(X41)
      | r1_tarski(k9_relat_1(X41,X40),k2_relat_1(X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).

cnf(c_0_86,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_87,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_75])).

cnf(c_0_88,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_89,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_77])).

cnf(c_0_90,plain,
    ( v5_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_75])).

cnf(c_0_91,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk5_0,esk4_0),k2_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_92,negated_conjecture,
    ( k7_relset_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk5_0,X1) = k9_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_36])).

cnf(c_0_93,negated_conjecture,
    ( k2_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,X1)) = k9_relat_1(esk5_0,k2_enumset1(esk2_0,esk2_0,esk2_0,X1))
    | r1_tarski(esk5_0,k1_xboole_0)
    | ~ r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_94,negated_conjecture,
    ( k9_relat_1(esk5_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) = k2_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_95,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_96,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_97,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])])).

cnf(c_0_98,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk5_0,esk4_0),k2_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( k2_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0)) = k2_relat_1(esk5_0)
    | r1_tarski(esk5_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_82]),c_0_94])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk5_0,X1),k2_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_41])).

cnf(c_0_101,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X1),k2_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_89])).

cnf(c_0_102,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(esk5_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100])])).

cnf(c_0_104,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X1),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_105,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_103]),c_0_87])])).

cnf(c_0_106,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_104]),c_0_87])])).

cnf(c_0_107,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_105]),c_0_106]),c_0_105]),c_0_105]),c_0_105]),c_0_105]),c_0_87])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:03:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.37/0.59  # AutoSched0-Mode selected heuristic G_E___208_C12_02_nc_F1_SE_CS_SP_PS_S002A
% 0.37/0.59  # and selection function SelectNegativeLiterals.
% 0.37/0.59  #
% 0.37/0.59  # Preprocessing time       : 0.028 s
% 0.37/0.59  # Presaturation interreduction done
% 0.37/0.59  
% 0.37/0.59  # Proof found!
% 0.37/0.59  # SZS status Theorem
% 0.37/0.59  # SZS output start CNFRefutation
% 0.37/0.59  fof(t64_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 0.37/0.59  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.37/0.59  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.37/0.59  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.37/0.59  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.37/0.59  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.37/0.59  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.37/0.59  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.37/0.59  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.37/0.59  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.37/0.59  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.37/0.59  fof(t118_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k1_relat_1(X3)))=>k9_relat_1(X3,k2_tarski(X1,X2))=k2_tarski(k1_funct_1(X3,X1),k1_funct_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_funct_1)).
% 0.37/0.59  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.37/0.59  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.37/0.59  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 0.37/0.59  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.37/0.59  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.37/0.59  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.37/0.59  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.37/0.59  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.37/0.59  fof(t144_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 0.37/0.59  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1)))))), inference(assume_negation,[status(cth)],[t64_funct_2])).
% 0.37/0.59  fof(c_0_22, plain, ![X32, X33]:(~v1_relat_1(X32)|(~m1_subset_1(X33,k1_zfmisc_1(X32))|v1_relat_1(X33))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.37/0.59  fof(c_0_23, plain, ![X38, X39]:v1_relat_1(k2_zfmisc_1(X38,X39)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.37/0.59  fof(c_0_24, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,k1_tarski(esk2_0),esk3_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))))&(esk3_0!=k1_xboole_0&~r1_tarski(k7_relset_1(k1_tarski(esk2_0),esk3_0,esk5_0,esk4_0),k1_tarski(k1_funct_1(esk5_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.37/0.59  fof(c_0_25, plain, ![X16]:k2_tarski(X16,X16)=k1_tarski(X16), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.37/0.59  fof(c_0_26, plain, ![X17, X18]:k1_enumset1(X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.37/0.59  fof(c_0_27, plain, ![X19, X20, X21]:k2_enumset1(X19,X19,X20,X21)=k1_enumset1(X19,X20,X21), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.37/0.59  cnf(c_0_28, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.37/0.59  cnf(c_0_29, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.37/0.59  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.37/0.59  cnf(c_0_31, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.37/0.59  cnf(c_0_32, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.37/0.59  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.37/0.59  fof(c_0_34, plain, ![X34, X35]:((~v4_relat_1(X35,X34)|r1_tarski(k1_relat_1(X35),X34)|~v1_relat_1(X35))&(~r1_tarski(k1_relat_1(X35),X34)|v4_relat_1(X35,X34)|~v1_relat_1(X35))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.37/0.59  cnf(c_0_35, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.37/0.59  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])).
% 0.37/0.59  fof(c_0_37, plain, ![X49, X50, X51]:((v4_relat_1(X51,X49)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))&(v5_relat_1(X51,X50)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.37/0.59  fof(c_0_38, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X10,X9)|(X10=X7|X10=X8)|X9!=k2_tarski(X7,X8))&((X11!=X7|r2_hidden(X11,X9)|X9!=k2_tarski(X7,X8))&(X11!=X8|r2_hidden(X11,X9)|X9!=k2_tarski(X7,X8))))&(((esk1_3(X12,X13,X14)!=X12|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_tarski(X12,X13))&(esk1_3(X12,X13,X14)!=X13|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_tarski(X12,X13)))&(r2_hidden(esk1_3(X12,X13,X14),X14)|(esk1_3(X12,X13,X14)=X12|esk1_3(X12,X13,X14)=X13)|X14=k2_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.37/0.59  fof(c_0_39, plain, ![X22, X23]:((~r1_tarski(X22,k1_tarski(X23))|(X22=k1_xboole_0|X22=k1_tarski(X23)))&((X22!=k1_xboole_0|r1_tarski(X22,k1_tarski(X23)))&(X22!=k1_tarski(X23)|r1_tarski(X22,k1_tarski(X23))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.37/0.59  cnf(c_0_40, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.37/0.59  cnf(c_0_41, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.37/0.59  cnf(c_0_42, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.37/0.59  fof(c_0_43, plain, ![X56]:(((v1_funct_1(X56)|(~v1_relat_1(X56)|~v1_funct_1(X56)))&(v1_funct_2(X56,k1_relat_1(X56),k2_relat_1(X56))|(~v1_relat_1(X56)|~v1_funct_1(X56))))&(m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X56),k2_relat_1(X56))))|(~v1_relat_1(X56)|~v1_funct_1(X56)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.37/0.59  cnf(c_0_44, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.37/0.59  cnf(c_0_45, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.37/0.59  cnf(c_0_46, negated_conjecture, (r1_tarski(k1_relat_1(esk5_0),X1)|~v4_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.37/0.59  cnf(c_0_47, negated_conjecture, (v4_relat_1(esk5_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_42, c_0_36])).
% 0.37/0.59  fof(c_0_48, plain, ![X46, X47, X48]:(~v1_relat_1(X48)|~v1_funct_1(X48)|(~r2_hidden(X46,k1_relat_1(X48))|~r2_hidden(X47,k1_relat_1(X48))|k9_relat_1(X48,k2_tarski(X46,X47))=k2_tarski(k1_funct_1(X48,X46),k1_funct_1(X48,X47)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_funct_1])])).
% 0.37/0.59  fof(c_0_49, plain, ![X27, X28]:((~m1_subset_1(X27,k1_zfmisc_1(X28))|r1_tarski(X27,X28))&(~r1_tarski(X27,X28)|m1_subset_1(X27,k1_zfmisc_1(X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.37/0.59  cnf(c_0_50, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.37/0.59  cnf(c_0_51, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.37/0.59  cnf(c_0_52, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_32]), c_0_33])).
% 0.37/0.59  cnf(c_0_53, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|~r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.37/0.59  cnf(c_0_54, negated_conjecture, (r1_tarski(k1_relat_1(esk5_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.37/0.59  fof(c_0_55, plain, ![X24, X25]:((k2_zfmisc_1(X24,X25)!=k1_xboole_0|(X24=k1_xboole_0|X25=k1_xboole_0))&((X24!=k1_xboole_0|k2_zfmisc_1(X24,X25)=k1_xboole_0)&(X25!=k1_xboole_0|k2_zfmisc_1(X24,X25)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.37/0.59  fof(c_0_56, plain, ![X44, X45]:(~v1_relat_1(X45)|~v4_relat_1(X45,X44)|X45=k7_relat_1(X45,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.37/0.59  cnf(c_0_57, plain, (k9_relat_1(X1,k2_tarski(X2,X3))=k2_tarski(k1_funct_1(X1,X2),k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.37/0.59  cnf(c_0_58, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.37/0.59  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),k2_relat_1(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_41]), c_0_51])])).
% 0.37/0.59  cnf(c_0_60, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_52])])).
% 0.37/0.59  cnf(c_0_61, negated_conjecture, (k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)=k1_relat_1(esk5_0)|k1_relat_1(esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.37/0.59  cnf(c_0_62, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.37/0.59  fof(c_0_63, plain, ![X42, X43]:(~v1_relat_1(X43)|k2_relat_1(k7_relat_1(X43,X42))=k9_relat_1(X43,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.37/0.59  cnf(c_0_64, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.37/0.59  fof(c_0_65, plain, ![X26]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X26)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.37/0.59  cnf(c_0_66, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.37/0.59  fof(c_0_67, plain, ![X52, X53, X54, X55]:(~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|k7_relset_1(X52,X53,X54,X55)=k9_relat_1(X54,X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.37/0.59  cnf(c_0_68, plain, (k9_relat_1(X1,k2_enumset1(X2,X2,X2,X3))=k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))|~r2_hidden(X2,k1_relat_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.37/0.59  cnf(c_0_69, negated_conjecture, (r1_tarski(esk5_0,k2_zfmisc_1(k1_relat_1(esk5_0),k2_relat_1(esk5_0)))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.37/0.59  cnf(c_0_70, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|r2_hidden(esk2_0,k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.37/0.59  cnf(c_0_71, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_62])).
% 0.37/0.59  cnf(c_0_72, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.37/0.59  cnf(c_0_73, negated_conjecture, (k7_relat_1(esk5_0,X1)=esk5_0|~v4_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_64, c_0_41])).
% 0.37/0.59  fof(c_0_74, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.37/0.59  cnf(c_0_75, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.37/0.59  fof(c_0_76, plain, ![X36, X37]:((~v5_relat_1(X37,X36)|r1_tarski(k2_relat_1(X37),X36)|~v1_relat_1(X37))&(~r1_tarski(k2_relat_1(X37),X36)|v5_relat_1(X37,X36)|~v1_relat_1(X37))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.37/0.59  cnf(c_0_77, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_66])).
% 0.37/0.59  cnf(c_0_78, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.37/0.59  cnf(c_0_79, negated_conjecture, (~r1_tarski(k7_relset_1(k1_tarski(esk2_0),esk3_0,esk5_0,esk4_0),k1_tarski(k1_funct_1(esk5_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.37/0.59  cnf(c_0_80, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.37/0.59  cnf(c_0_81, negated_conjecture, (k2_enumset1(k1_funct_1(esk5_0,X1),k1_funct_1(esk5_0,X1),k1_funct_1(esk5_0,X1),k1_funct_1(esk5_0,X2))=k9_relat_1(esk5_0,k2_enumset1(X1,X1,X1,X2))|~r2_hidden(X2,k1_relat_1(esk5_0))|~r2_hidden(X1,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_41]), c_0_51])])).
% 0.37/0.59  cnf(c_0_82, negated_conjecture, (r2_hidden(esk2_0,k1_relat_1(esk5_0))|r1_tarski(esk5_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])).
% 0.37/0.59  cnf(c_0_83, negated_conjecture, (k2_relat_1(k7_relat_1(esk5_0,X1))=k9_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_72, c_0_41])).
% 0.37/0.59  cnf(c_0_84, negated_conjecture, (k7_relat_1(esk5_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))=esk5_0), inference(spm,[status(thm)],[c_0_73, c_0_47])).
% 0.37/0.59  fof(c_0_85, plain, ![X40, X41]:(~v1_relat_1(X41)|r1_tarski(k9_relat_1(X41,X40),k2_relat_1(X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).
% 0.37/0.59  cnf(c_0_86, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.37/0.59  cnf(c_0_87, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_58, c_0_75])).
% 0.37/0.59  cnf(c_0_88, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.37/0.59  cnf(c_0_89, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_29, c_0_77])).
% 0.37/0.59  cnf(c_0_90, plain, (v5_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_78, c_0_75])).
% 0.37/0.59  cnf(c_0_91, negated_conjecture, (~r1_tarski(k7_relset_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk5_0,esk4_0),k2_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.37/0.59  cnf(c_0_92, negated_conjecture, (k7_relset_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk5_0,X1)=k9_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_80, c_0_36])).
% 0.37/0.59  cnf(c_0_93, negated_conjecture, (k2_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,X1))=k9_relat_1(esk5_0,k2_enumset1(esk2_0,esk2_0,esk2_0,X1))|r1_tarski(esk5_0,k1_xboole_0)|~r2_hidden(X1,k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.37/0.59  cnf(c_0_94, negated_conjecture, (k9_relat_1(esk5_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))=k2_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.37/0.59  cnf(c_0_95, plain, (r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.37/0.59  cnf(c_0_96, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.37/0.59  cnf(c_0_97, plain, (r1_tarski(k2_relat_1(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90])])).
% 0.37/0.59  cnf(c_0_98, negated_conjecture, (~r1_tarski(k9_relat_1(esk5_0,esk4_0),k2_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0)))), inference(rw,[status(thm)],[c_0_91, c_0_92])).
% 0.37/0.59  cnf(c_0_99, negated_conjecture, (k2_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0))=k2_relat_1(esk5_0)|r1_tarski(esk5_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_82]), c_0_94])).
% 0.37/0.59  cnf(c_0_100, negated_conjecture, (r1_tarski(k9_relat_1(esk5_0,X1),k2_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_95, c_0_41])).
% 0.37/0.59  cnf(c_0_101, plain, (r1_tarski(k9_relat_1(k1_xboole_0,X1),k2_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_95, c_0_89])).
% 0.37/0.59  cnf(c_0_102, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.37/0.59  cnf(c_0_103, negated_conjecture, (r1_tarski(esk5_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100])])).
% 0.37/0.59  cnf(c_0_104, plain, (r1_tarski(k9_relat_1(k1_xboole_0,X1),k1_xboole_0)), inference(rw,[status(thm)],[c_0_101, c_0_102])).
% 0.37/0.59  cnf(c_0_105, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_103]), c_0_87])])).
% 0.37/0.59  cnf(c_0_106, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_104]), c_0_87])])).
% 0.37/0.59  cnf(c_0_107, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_105]), c_0_106]), c_0_105]), c_0_105]), c_0_105]), c_0_105]), c_0_87])]), ['proof']).
% 0.37/0.59  # SZS output end CNFRefutation
% 0.37/0.59  # Proof object total steps             : 108
% 0.37/0.59  # Proof object clause steps            : 65
% 0.37/0.59  # Proof object formula steps           : 43
% 0.37/0.59  # Proof object conjectures             : 30
% 0.37/0.59  # Proof object clause conjectures      : 27
% 0.37/0.59  # Proof object formula conjectures     : 3
% 0.37/0.59  # Proof object initial clauses used    : 25
% 0.37/0.59  # Proof object initial formulas used   : 21
% 0.37/0.59  # Proof object generating inferences   : 29
% 0.37/0.59  # Proof object simplifying inferences  : 49
% 0.37/0.59  # Training examples: 0 positive, 0 negative
% 0.37/0.59  # Parsed axioms                        : 22
% 0.37/0.59  # Removed by relevancy pruning/SinE    : 0
% 0.37/0.59  # Initial clauses                      : 43
% 0.37/0.59  # Removed in clause preprocessing      : 4
% 0.37/0.59  # Initial clauses in saturation        : 39
% 0.37/0.59  # Processed clauses                    : 1017
% 0.37/0.59  # ...of these trivial                  : 9
% 0.37/0.59  # ...subsumed                          : 480
% 0.37/0.59  # ...remaining for further processing  : 528
% 0.37/0.59  # Other redundant clauses eliminated   : 163
% 0.37/0.59  # Clauses deleted for lack of memory   : 0
% 0.37/0.59  # Backward-subsumed                    : 76
% 0.37/0.59  # Backward-rewritten                   : 281
% 0.37/0.59  # Generated clauses                    : 7466
% 0.37/0.59  # ...of the previous two non-trivial   : 6862
% 0.37/0.59  # Contextual simplify-reflections      : 7
% 0.37/0.59  # Paramodulations                      : 7197
% 0.37/0.59  # Factorizations                       : 108
% 0.37/0.59  # Equation resolutions                 : 163
% 0.37/0.59  # Propositional unsat checks           : 0
% 0.37/0.59  #    Propositional check models        : 0
% 0.37/0.59  #    Propositional check unsatisfiable : 0
% 0.37/0.59  #    Propositional clauses             : 0
% 0.37/0.59  #    Propositional clauses after purity: 0
% 0.37/0.59  #    Propositional unsat core size     : 0
% 0.37/0.59  #    Propositional preprocessing time  : 0.000
% 0.37/0.59  #    Propositional encoding time       : 0.000
% 0.37/0.59  #    Propositional solver time         : 0.000
% 0.37/0.59  #    Success case prop preproc time    : 0.000
% 0.37/0.59  #    Success case prop encoding time   : 0.000
% 0.37/0.59  #    Success case prop solver time     : 0.000
% 0.37/0.59  # Current number of processed clauses  : 125
% 0.37/0.59  #    Positive orientable unit clauses  : 43
% 0.37/0.59  #    Positive unorientable unit clauses: 0
% 0.37/0.59  #    Negative unit clauses             : 1
% 0.37/0.59  #    Non-unit-clauses                  : 81
% 0.37/0.59  # Current number of unprocessed clauses: 5480
% 0.37/0.59  # ...number of literals in the above   : 43541
% 0.37/0.59  # Current number of archived formulas  : 0
% 0.37/0.59  # Current number of archived clauses   : 397
% 0.37/0.59  # Clause-clause subsumption calls (NU) : 39467
% 0.37/0.59  # Rec. Clause-clause subsumption calls : 8649
% 0.37/0.59  # Non-unit clause-clause subsumptions  : 538
% 0.37/0.59  # Unit Clause-clause subsumption calls : 5588
% 0.37/0.59  # Rewrite failures with RHS unbound    : 0
% 0.37/0.59  # BW rewrite match attempts            : 99
% 0.37/0.59  # BW rewrite match successes           : 13
% 0.37/0.59  # Condensation attempts                : 0
% 0.37/0.59  # Condensation successes               : 0
% 0.37/0.59  # Termbank termtop insertions          : 232677
% 0.37/0.60  
% 0.37/0.60  # -------------------------------------------------
% 0.37/0.60  # User time                : 0.237 s
% 0.37/0.60  # System time              : 0.005 s
% 0.37/0.60  # Total time               : 0.243 s
% 0.37/0.60  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
