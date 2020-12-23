%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:57:12 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 179 expanded)
%              Number of clauses        :   42 (  77 expanded)
%              Number of leaves         :   17 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :  167 ( 311 expanded)
%              Number of equality atoms :   18 (  70 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t19_relset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => r1_tarski(k3_relat_1(X3),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

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

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(cc6_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X2))
         => v5_relat_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_relat_1)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(cc5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X2))
         => v4_relat_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_relat_1)).

fof(c_0_17,plain,(
    ! [X16,X17] : k3_tarski(k2_tarski(X16,X17)) = k2_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X11,X12] : k1_enumset1(X11,X11,X12) = k2_tarski(X11,X12) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => r1_tarski(k3_relat_1(X3),k2_xboole_0(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t19_relset_1])).

fof(c_0_20,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X8,X7)
      | r1_tarski(k2_xboole_0(X6,X8),X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_21,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X13,X14,X15] : k2_enumset1(X13,X13,X14,X15) = k1_enumset1(X13,X14,X15) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X35] :
      ( ~ v1_relat_1(X35)
      | k3_relat_1(X35) = k2_xboole_0(k1_relat_1(X35),k2_relat_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_25,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & ~ r1_tarski(k3_relat_1(esk3_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_26,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | v1_relat_1(X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_31,plain,(
    ! [X36,X37] : v1_relat_1(k2_zfmisc_1(X36,X37)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk3_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r1_tarski(k3_tarski(k2_enumset1(X1,X1,X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_34,plain,
    ( k3_relat_1(X1) = k3_tarski(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_27]),c_0_28])).

cnf(c_0_35,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_38,plain,(
    ! [X38,X39,X40] :
      ( ( v4_relat_1(X40,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( v5_relat_1(X40,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_39,plain,(
    ! [X21,X22] :
      ( ( ~ m1_subset_1(X21,k1_zfmisc_1(X22))
        | r1_tarski(X21,X22) )
      & ( ~ r1_tarski(X21,X22)
        | m1_subset_1(X21,k1_zfmisc_1(X22)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk3_0),k3_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_27]),c_0_28])).

cnf(c_0_41,plain,
    ( r1_tarski(k3_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

fof(c_0_43,plain,(
    ! [X33,X34] :
      ( ( ~ v5_relat_1(X34,X33)
        | r1_tarski(k2_relat_1(X34),X33)
        | ~ v1_relat_1(X34) )
      & ( ~ r1_tarski(k2_relat_1(X34),X33)
        | v5_relat_1(X34,X33)
        | ~ v1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_44,plain,(
    ! [X28,X29,X30] :
      ( ~ v1_relat_1(X29)
      | ~ v5_relat_1(X29,X28)
      | ~ m1_subset_1(X30,k1_zfmisc_1(X29))
      | v5_relat_1(X30,X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc6_relat_1])])])).

cnf(c_0_45,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_47,plain,(
    ! [X18,X19,X20] :
      ( ( r1_tarski(k2_zfmisc_1(X18,X20),k2_zfmisc_1(X19,X20))
        | ~ r1_tarski(X18,X19) )
      & ( r1_tarski(k2_zfmisc_1(X20,X18),k2_zfmisc_1(X20,X19))
        | ~ r1_tarski(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

fof(c_0_48,plain,(
    ! [X4,X5] : r1_tarski(X4,k2_xboole_0(X4,X5)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_49,plain,(
    ! [X9,X10] : k2_tarski(X9,X10) = k2_tarski(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk3_0),k3_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))
    | ~ r1_tarski(k1_relat_1(esk3_0),k3_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_51,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_52,plain,(
    ! [X31,X32] :
      ( ( ~ v4_relat_1(X32,X31)
        | r1_tarski(k1_relat_1(X32),X31)
        | ~ v1_relat_1(X32) )
      & ( ~ r1_tarski(k1_relat_1(X32),X31)
        | v4_relat_1(X32,X31)
        | ~ v1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_53,plain,
    ( v5_relat_1(X3,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_58,plain,(
    ! [X25,X26,X27] :
      ( ~ v1_relat_1(X26)
      | ~ v4_relat_1(X26,X25)
      | ~ m1_subset_1(X27,k1_zfmisc_1(X26))
      | v4_relat_1(X27,X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc5_relat_1])])])).

cnf(c_0_59,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_60,negated_conjecture,
    ( ~ v5_relat_1(esk3_0,k3_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))
    | ~ r1_tarski(k1_relat_1(esk3_0),k3_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_42])])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( v5_relat_1(esk3_0,X1)
    | ~ v5_relat_1(k2_zfmisc_1(esk1_0,esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_36]),c_0_37])])).

cnf(c_0_63,plain,
    ( v5_relat_1(k2_zfmisc_1(X1,X2),X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_27]),c_0_28])).

cnf(c_0_65,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_22]),c_0_22]),c_0_28]),c_0_28])).

cnf(c_0_66,plain,
    ( v4_relat_1(X3,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_46])).

cnf(c_0_68,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_69,negated_conjecture,
    ( ~ v5_relat_1(esk3_0,k3_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))
    | ~ v4_relat_1(esk3_0,k3_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_42])])).

cnf(c_0_70,negated_conjecture,
    ( v5_relat_1(esk3_0,X1)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( v4_relat_1(esk3_0,X1)
    | ~ v4_relat_1(k2_zfmisc_1(esk1_0,esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_36]),c_0_37])])).

cnf(c_0_73,plain,
    ( v4_relat_1(k2_zfmisc_1(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( ~ v4_relat_1(esk3_0,k3_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])])).

cnf(c_0_75,negated_conjecture,
    ( v4_relat_1(esk3_0,X1)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_64])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:58:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.21/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.027 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.21/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.39  fof(t19_relset_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>r1_tarski(k3_relat_1(X3),k2_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relset_1)).
% 0.21/0.39  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.21/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.39  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 0.21/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.21/0.39  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.21/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.39  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.21/0.39  fof(cc6_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X2))=>v5_relat_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_relat_1)).
% 0.21/0.39  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 0.21/0.39  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.21/0.39  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.21/0.39  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.21/0.39  fof(cc5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X2))=>v4_relat_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_relat_1)).
% 0.21/0.39  fof(c_0_17, plain, ![X16, X17]:k3_tarski(k2_tarski(X16,X17))=k2_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.21/0.39  fof(c_0_18, plain, ![X11, X12]:k1_enumset1(X11,X11,X12)=k2_tarski(X11,X12), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.39  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>r1_tarski(k3_relat_1(X3),k2_xboole_0(X1,X2)))), inference(assume_negation,[status(cth)],[t19_relset_1])).
% 0.21/0.39  fof(c_0_20, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X8,X7)|r1_tarski(k2_xboole_0(X6,X8),X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.21/0.39  cnf(c_0_21, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.39  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.39  fof(c_0_23, plain, ![X13, X14, X15]:k2_enumset1(X13,X13,X14,X15)=k1_enumset1(X13,X14,X15), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.39  fof(c_0_24, plain, ![X35]:(~v1_relat_1(X35)|k3_relat_1(X35)=k2_xboole_0(k1_relat_1(X35),k2_relat_1(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.21/0.39  fof(c_0_25, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))&~r1_tarski(k3_relat_1(esk3_0),k2_xboole_0(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.21/0.39  cnf(c_0_26, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.39  cnf(c_0_27, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.39  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.39  cnf(c_0_29, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.39  fof(c_0_30, plain, ![X23, X24]:(~v1_relat_1(X23)|(~m1_subset_1(X24,k1_zfmisc_1(X23))|v1_relat_1(X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.39  fof(c_0_31, plain, ![X36, X37]:v1_relat_1(k2_zfmisc_1(X36,X37)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.21/0.39  cnf(c_0_32, negated_conjecture, (~r1_tarski(k3_relat_1(esk3_0),k2_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.39  cnf(c_0_33, plain, (r1_tarski(k3_tarski(k2_enumset1(X1,X1,X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.21/0.39  cnf(c_0_34, plain, (k3_relat_1(X1)=k3_tarski(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_27]), c_0_28])).
% 0.21/0.39  cnf(c_0_35, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.39  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.39  cnf(c_0_37, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.39  fof(c_0_38, plain, ![X38, X39, X40]:((v4_relat_1(X40,X38)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(v5_relat_1(X40,X39)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.21/0.39  fof(c_0_39, plain, ![X21, X22]:((~m1_subset_1(X21,k1_zfmisc_1(X22))|r1_tarski(X21,X22))&(~r1_tarski(X21,X22)|m1_subset_1(X21,k1_zfmisc_1(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.39  cnf(c_0_40, negated_conjecture, (~r1_tarski(k3_relat_1(esk3_0),k3_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_27]), c_0_28])).
% 0.21/0.39  cnf(c_0_41, plain, (r1_tarski(k3_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.39  cnf(c_0_42, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.21/0.39  fof(c_0_43, plain, ![X33, X34]:((~v5_relat_1(X34,X33)|r1_tarski(k2_relat_1(X34),X33)|~v1_relat_1(X34))&(~r1_tarski(k2_relat_1(X34),X33)|v5_relat_1(X34,X33)|~v1_relat_1(X34))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.21/0.39  fof(c_0_44, plain, ![X28, X29, X30]:(~v1_relat_1(X29)|~v5_relat_1(X29,X28)|(~m1_subset_1(X30,k1_zfmisc_1(X29))|v5_relat_1(X30,X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc6_relat_1])])])).
% 0.21/0.39  cnf(c_0_45, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.39  cnf(c_0_46, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.39  fof(c_0_47, plain, ![X18, X19, X20]:((r1_tarski(k2_zfmisc_1(X18,X20),k2_zfmisc_1(X19,X20))|~r1_tarski(X18,X19))&(r1_tarski(k2_zfmisc_1(X20,X18),k2_zfmisc_1(X20,X19))|~r1_tarski(X18,X19))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 0.21/0.39  fof(c_0_48, plain, ![X4, X5]:r1_tarski(X4,k2_xboole_0(X4,X5)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.21/0.39  fof(c_0_49, plain, ![X9, X10]:k2_tarski(X9,X10)=k2_tarski(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.21/0.39  cnf(c_0_50, negated_conjecture, (~r1_tarski(k2_relat_1(esk3_0),k3_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))|~r1_tarski(k1_relat_1(esk3_0),k3_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.21/0.39  cnf(c_0_51, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.39  fof(c_0_52, plain, ![X31, X32]:((~v4_relat_1(X32,X31)|r1_tarski(k1_relat_1(X32),X31)|~v1_relat_1(X32))&(~r1_tarski(k1_relat_1(X32),X31)|v4_relat_1(X32,X31)|~v1_relat_1(X32))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.21/0.39  cnf(c_0_53, plain, (v5_relat_1(X3,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.39  cnf(c_0_54, plain, (v5_relat_1(X1,X2)|~r1_tarski(X1,k2_zfmisc_1(X3,X2))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.21/0.39  cnf(c_0_55, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.39  cnf(c_0_56, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.39  cnf(c_0_57, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.39  fof(c_0_58, plain, ![X25, X26, X27]:(~v1_relat_1(X26)|~v4_relat_1(X26,X25)|(~m1_subset_1(X27,k1_zfmisc_1(X26))|v4_relat_1(X27,X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc5_relat_1])])])).
% 0.21/0.39  cnf(c_0_59, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.39  cnf(c_0_60, negated_conjecture, (~v5_relat_1(esk3_0,k3_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))|~r1_tarski(k1_relat_1(esk3_0),k3_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_42])])).
% 0.21/0.39  cnf(c_0_61, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.21/0.39  cnf(c_0_62, negated_conjecture, (v5_relat_1(esk3_0,X1)|~v5_relat_1(k2_zfmisc_1(esk1_0,esk2_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_36]), c_0_37])])).
% 0.21/0.39  cnf(c_0_63, plain, (v5_relat_1(k2_zfmisc_1(X1,X2),X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.39  cnf(c_0_64, plain, (r1_tarski(X1,k3_tarski(k2_enumset1(X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_27]), c_0_28])).
% 0.21/0.39  cnf(c_0_65, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_22]), c_0_22]), c_0_28]), c_0_28])).
% 0.21/0.39  cnf(c_0_66, plain, (v4_relat_1(X3,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.21/0.39  cnf(c_0_67, plain, (v4_relat_1(X1,X2)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_59, c_0_46])).
% 0.21/0.39  cnf(c_0_68, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.39  cnf(c_0_69, negated_conjecture, (~v5_relat_1(esk3_0,k3_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))|~v4_relat_1(esk3_0,k3_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_42])])).
% 0.21/0.39  cnf(c_0_70, negated_conjecture, (v5_relat_1(esk3_0,X1)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.21/0.39  cnf(c_0_71, plain, (r1_tarski(X1,k3_tarski(k2_enumset1(X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.21/0.39  cnf(c_0_72, negated_conjecture, (v4_relat_1(esk3_0,X1)|~v4_relat_1(k2_zfmisc_1(esk1_0,esk2_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_36]), c_0_37])])).
% 0.21/0.39  cnf(c_0_73, plain, (v4_relat_1(k2_zfmisc_1(X1,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.21/0.39  cnf(c_0_74, negated_conjecture, (~v4_relat_1(esk3_0,k3_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])])).
% 0.21/0.39  cnf(c_0_75, negated_conjecture, (v4_relat_1(esk3_0,X1)|~r1_tarski(esk1_0,X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.21/0.39  cnf(c_0_76, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_64])]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 77
% 0.21/0.39  # Proof object clause steps            : 42
% 0.21/0.39  # Proof object formula steps           : 35
% 0.21/0.39  # Proof object conjectures             : 16
% 0.21/0.39  # Proof object clause conjectures      : 13
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 20
% 0.21/0.39  # Proof object initial formulas used   : 17
% 0.21/0.39  # Proof object generating inferences   : 16
% 0.21/0.39  # Proof object simplifying inferences  : 29
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 17
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 23
% 0.21/0.39  # Removed in clause preprocessing      : 3
% 0.21/0.39  # Initial clauses in saturation        : 20
% 0.21/0.39  # Processed clauses                    : 198
% 0.21/0.39  # ...of these trivial                  : 1
% 0.21/0.39  # ...subsumed                          : 42
% 0.21/0.39  # ...remaining for further processing  : 155
% 0.21/0.39  # Other redundant clauses eliminated   : 0
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 2
% 0.21/0.39  # Backward-rewritten                   : 1
% 0.21/0.39  # Generated clauses                    : 352
% 0.21/0.39  # ...of the previous two non-trivial   : 330
% 0.21/0.39  # Contextual simplify-reflections      : 2
% 0.21/0.39  # Paramodulations                      : 352
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 0
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 132
% 0.21/0.39  #    Positive orientable unit clauses  : 18
% 0.21/0.39  #    Positive unorientable unit clauses: 1
% 0.21/0.39  #    Negative unit clauses             : 2
% 0.21/0.39  #    Non-unit-clauses                  : 111
% 0.21/0.39  # Current number of unprocessed clauses: 161
% 0.21/0.39  # ...number of literals in the above   : 566
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 26
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 1581
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 1064
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 44
% 0.21/0.39  # Unit Clause-clause subsumption calls : 21
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 21
% 0.21/0.39  # BW rewrite match successes           : 11
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 6691
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.038 s
% 0.21/0.39  # System time              : 0.004 s
% 0.21/0.39  # Total time               : 0.043 s
% 0.21/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
