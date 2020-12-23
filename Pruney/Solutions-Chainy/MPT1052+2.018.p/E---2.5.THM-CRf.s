%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:16 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  126 (34839 expanded)
%              Number of clauses        :   89 (15753 expanded)
%              Number of leaves         :   19 (8635 expanded)
%              Depth                    :   24
%              Number of atoms          :  310 (98276 expanded)
%              Number of equality atoms :  140 (32370 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t169_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( k1_relat_1(X3) = X1
          & r1_tarski(k2_relat_1(X3),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_2)).

fof(t121_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X3,k1_funct_2(X1,X2))
     => ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

fof(t160_funct_2,axiom,(
    ! [X1,X2] : k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)) = k1_funct_2(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_funct_2)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(t195_relat_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t193_relat_1,axiom,(
    ! [X1,X2] : r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

fof(t194_relat_1,axiom,(
    ! [X1,X2] : r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(fc3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & v1_xboole_0(X2) )
     => v1_xboole_0(k1_funct_2(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X3,k1_funct_2(X1,X2))
         => ( k1_relat_1(X3) = X1
            & r1_tarski(k2_relat_1(X3),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t169_funct_2])).

fof(c_0_20,plain,(
    ! [X32,X33,X34] :
      ( ( v1_funct_1(X34)
        | ~ r2_hidden(X34,k1_funct_2(X32,X33)) )
      & ( v1_funct_2(X34,X32,X33)
        | ~ r2_hidden(X34,k1_funct_2(X32,X33)) )
      & ( m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
        | ~ r2_hidden(X34,k1_funct_2(X32,X33)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_2])])])).

fof(c_0_21,plain,(
    ! [X35,X36] : k5_partfun1(X35,X36,k3_partfun1(k1_xboole_0,X35,X36)) = k1_funct_2(X35,X36) ),
    inference(variable_rename,[status(thm)],[t160_funct_2])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & r2_hidden(esk4_0,k1_funct_2(esk2_0,esk3_0))
    & ( k1_relat_1(esk4_0) != esk2_0
      | ~ r1_tarski(k2_relat_1(esk4_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)) = k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk4_0,k1_funct_2(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X21,X22] :
      ( ( r1_tarski(k1_relat_1(X21),k1_relat_1(X22))
        | ~ r1_tarski(X21,X22)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) )
      & ( r1_tarski(k2_relat_1(X21),k2_relat_1(X22))
        | ~ r1_tarski(X21,X22)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_28,plain,(
    ! [X19,X20] :
      ( ( k1_relat_1(k2_zfmisc_1(X19,X20)) = X19
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0 )
      & ( k2_relat_1(k2_zfmisc_1(X19,X20)) = X20
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).

fof(c_0_29,plain,(
    ! [X13,X14] : v1_relat_1(k2_zfmisc_1(X13,X14)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_30,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk4_0,k5_partfun1(esk2_0,esk3_0,k3_partfun1(k1_xboole_0,esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_24])).

fof(c_0_33,plain,(
    ! [X27,X28,X29] :
      ( ( ~ v1_funct_2(X29,X27,X28)
        | X27 = k1_relset_1(X27,X28,X29)
        | X28 = k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( X27 != k1_relset_1(X27,X28,X29)
        | v1_funct_2(X29,X27,X28)
        | X28 = k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( ~ v1_funct_2(X29,X27,X28)
        | X27 = k1_relset_1(X27,X28,X29)
        | X27 != k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( X27 != k1_relset_1(X27,X28,X29)
        | v1_funct_2(X29,X27,X28)
        | X27 != k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( ~ v1_funct_2(X29,X27,X28)
        | X29 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 != k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( X29 != k1_xboole_0
        | v1_funct_2(X29,X27,X28)
        | X27 = k1_xboole_0
        | X28 != k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_34,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_35,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_40,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | k1_relset_1(X24,X25,X26) = k1_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_41,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_32])).

fof(c_0_43,plain,(
    ! [X23] :
      ( ( k1_relat_1(X23) != k1_xboole_0
        | X23 = k1_xboole_0
        | ~ v1_relat_1(X23) )
      & ( k2_relat_1(X23) != k1_xboole_0
        | X23 = k1_xboole_0
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_44,plain,(
    ! [X10] :
      ( ~ r1_tarski(X10,k1_xboole_0)
      | X10 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_45,plain,(
    ! [X15,X16] : r1_tarski(k1_relat_1(k2_zfmisc_1(X15,X16)),X15) ),
    inference(variable_rename,[status(thm)],[t193_relat_1])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r1_tarski(k2_relat_1(X3),X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_49,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk4_0) = esk2_0
    | k1_xboole_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_39]),c_0_42])])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( k1_relat_1(esk4_0) != esk2_0
    | ~ r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_55,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | k1_xboole_0 = esk2_0
    | r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_56,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0
    | k1_xboole_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_39])])).

cnf(c_0_57,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | k1_relat_1(k2_zfmisc_1(X1,X2)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_37])).

cnf(c_0_58,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | k1_xboole_0 = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_60,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | esk3_0 != esk2_0 ),
    inference(ef,[status(thm)],[c_0_59])).

fof(c_0_62,plain,(
    ! [X17,X18] : r1_tarski(k2_relat_1(k2_zfmisc_1(X17,X18)),X18) ),
    inference(variable_rename,[status(thm)],[t194_relat_1])).

cnf(c_0_63,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,X1) = esk2_0
    | esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_60])).

cnf(c_0_65,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_66,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_67,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0)
    | esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( v1_relat_1(esk2_0)
    | esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_61])).

cnf(c_0_70,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_71,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_72,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_65])).

cnf(c_0_73,plain,
    ( r1_tarski(k2_relat_1(X1),k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_66]),c_0_64])])).

fof(c_0_74,plain,(
    ! [X9] : r1_tarski(k1_xboole_0,X9) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),k1_relat_1(esk2_0))
    | esk3_0 != esk2_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_48])]),c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( k1_relat_1(esk2_0) = esk2_0
    | esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_61])).

cnf(c_0_77,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_37])])).

cnf(c_0_78,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_73])).

cnf(c_0_79,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( X1 = esk2_0
    | esk3_0 != esk2_0
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_61])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),esk2_0)
    | esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( k2_zfmisc_1(X1,esk3_0) = esk3_0
    | k1_xboole_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_59])).

cnf(c_0_83,negated_conjecture,
    ( k1_relat_1(esk4_0) != esk2_0
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_78]),c_0_79]),c_0_48])])).

cnf(c_0_84,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0
    | esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_85,plain,
    ( r1_tarski(k1_relat_1(k2_relat_1(X1)),k1_xboole_0)
    | ~ v1_relat_1(k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_73]),c_0_70]),c_0_64])])).

cnf(c_0_86,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk3_0
    | k1_xboole_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_59])).

cnf(c_0_87,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_59])).

cnf(c_0_88,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_59])).

cnf(c_0_89,negated_conjecture,
    ( k1_xboole_0 = esk4_0
    | k1_relat_1(esk4_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_48])).

cnf(c_0_90,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | X1 = esk3_0
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_59])).

cnf(c_0_91,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_82])).

cnf(c_0_92,negated_conjecture,
    ( esk3_0 != esk2_0
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_93,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | r1_tarski(k1_relat_1(esk3_0),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87]),c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | k1_xboole_0 = esk4_0
    | k1_xboole_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_89,c_0_56])).

cnf(c_0_95,negated_conjecture,
    ( esk3_0 = esk4_0
    | k1_xboole_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_96,negated_conjecture,
    ( esk3_0 != esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_61]),c_0_68])).

cnf(c_0_97,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_xboole_0
    | k1_xboole_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( esk3_0 = esk4_0
    | esk2_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96])).

cnf(c_0_99,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_56])).

fof(c_0_100,plain,(
    ! [X30,X31] :
      ( v1_xboole_0(X30)
      | ~ v1_xboole_0(X31)
      | v1_xboole_0(k1_funct_2(X30,X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_funct_2])])])).

cnf(c_0_101,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | esk2_0 = esk4_0
    | k1_xboole_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,X1) = esk2_0
    | esk3_0 = esk4_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_95])).

cnf(c_0_103,negated_conjecture,
    ( esk3_0 = esk4_0
    | ~ r1_tarski(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_95]),c_0_96])).

cnf(c_0_104,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(k1_funct_2(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

fof(c_0_105,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_106,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | esk2_0 = esk4_0
    | k1_xboole_0 = esk4_0 ),
    inference(spm,[status(thm)],[c_0_89,c_0_101])).

cnf(c_0_107,negated_conjecture,
    ( esk3_0 = esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_102]),c_0_103])).

fof(c_0_108,plain,(
    ! [X8] :
      ( ~ v1_xboole_0(X8)
      | X8 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_109,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | ~ v1_xboole_0(X2) ),
    inference(rw,[status(thm)],[c_0_104,c_0_24])).

cnf(c_0_110,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_111,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_112,negated_conjecture,
    ( k1_xboole_0 = esk4_0
    | esk2_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_106]),c_0_96])).

cnf(c_0_113,negated_conjecture,
    ( esk2_0 != esk4_0 ),
    inference(rw,[status(thm)],[c_0_96,c_0_107])).

cnf(c_0_114,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_115,plain,
    ( v1_xboole_0(k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0)))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_116,negated_conjecture,
    ( ~ v1_xboole_0(k5_partfun1(esk2_0,esk3_0,k3_partfun1(k1_xboole_0,esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_111,c_0_32])).

cnf(c_0_117,negated_conjecture,
    ( k1_xboole_0 = esk4_0 ),
    inference(sr,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_118,plain,
    ( k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0)) = k1_xboole_0
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_119,negated_conjecture,
    ( esk2_0 = esk4_0
    | v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_112])).

cnf(c_0_120,negated_conjecture,
    ( ~ v1_xboole_0(k5_partfun1(esk2_0,esk4_0,k3_partfun1(esk4_0,esk2_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_107]),c_0_107]),c_0_117])).

cnf(c_0_121,plain,
    ( k5_partfun1(X1,esk4_0,k3_partfun1(esk4_0,X1,esk4_0)) = esk4_0
    | v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_117]),c_0_117]),c_0_117]),c_0_117])).

cnf(c_0_122,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(sr,[status(thm)],[c_0_119,c_0_113])).

cnf(c_0_123,plain,
    ( X1 = esk4_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[c_0_114,c_0_117])).

cnf(c_0_124,negated_conjecture,
    ( v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_122])])).

cnf(c_0_125,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_113]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.028 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t169_funct_2, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X3,k1_funct_2(X1,X2))=>(k1_relat_1(X3)=X1&r1_tarski(k2_relat_1(X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_funct_2)).
% 0.20/0.42  fof(t121_funct_2, axiom, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 0.20/0.42  fof(t160_funct_2, axiom, ![X1, X2]:k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))=k1_funct_2(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_funct_2)).
% 0.20/0.42  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.20/0.42  fof(t195_relat_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((k1_relat_1(k2_zfmisc_1(X1,X2))=X1&k2_relat_1(k2_zfmisc_1(X1,X2))=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 0.20/0.42  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.42  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.42  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.42  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.42  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 0.20/0.42  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.20/0.42  fof(t193_relat_1, axiom, ![X1, X2]:r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_relat_1)).
% 0.20/0.42  fof(t194_relat_1, axiom, ![X1, X2]:r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t194_relat_1)).
% 0.20/0.42  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.20/0.42  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.42  fof(fc3_funct_2, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&v1_xboole_0(X2))=>v1_xboole_0(k1_funct_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_2)).
% 0.20/0.42  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.42  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.42  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.42  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X3,k1_funct_2(X1,X2))=>(k1_relat_1(X3)=X1&r1_tarski(k2_relat_1(X3),X2))))), inference(assume_negation,[status(cth)],[t169_funct_2])).
% 0.20/0.42  fof(c_0_20, plain, ![X32, X33, X34]:(((v1_funct_1(X34)|~r2_hidden(X34,k1_funct_2(X32,X33)))&(v1_funct_2(X34,X32,X33)|~r2_hidden(X34,k1_funct_2(X32,X33))))&(m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|~r2_hidden(X34,k1_funct_2(X32,X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_2])])])).
% 0.20/0.42  fof(c_0_21, plain, ![X35, X36]:k5_partfun1(X35,X36,k3_partfun1(k1_xboole_0,X35,X36))=k1_funct_2(X35,X36), inference(variable_rename,[status(thm)],[t160_funct_2])).
% 0.20/0.42  fof(c_0_22, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&(r2_hidden(esk4_0,k1_funct_2(esk2_0,esk3_0))&(k1_relat_1(esk4_0)!=esk2_0|~r1_tarski(k2_relat_1(esk4_0),esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.20/0.42  cnf(c_0_23, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.42  cnf(c_0_24, plain, (k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_25, negated_conjecture, (r2_hidden(esk4_0,k1_funct_2(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_26, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.42  fof(c_0_27, plain, ![X21, X22]:((r1_tarski(k1_relat_1(X21),k1_relat_1(X22))|~r1_tarski(X21,X22)|~v1_relat_1(X22)|~v1_relat_1(X21))&(r1_tarski(k2_relat_1(X21),k2_relat_1(X22))|~r1_tarski(X21,X22)|~v1_relat_1(X22)|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.20/0.42  fof(c_0_28, plain, ![X19, X20]:((k1_relat_1(k2_zfmisc_1(X19,X20))=X19|(X19=k1_xboole_0|X20=k1_xboole_0))&(k2_relat_1(k2_zfmisc_1(X19,X20))=X20|(X19=k1_xboole_0|X20=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).
% 0.20/0.42  fof(c_0_29, plain, ![X13, X14]:v1_relat_1(k2_zfmisc_1(X13,X14)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.42  fof(c_0_30, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.42  cnf(c_0_31, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3)))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.42  cnf(c_0_32, negated_conjecture, (r2_hidden(esk4_0,k5_partfun1(esk2_0,esk3_0,k3_partfun1(k1_xboole_0,esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_25, c_0_24])).
% 0.20/0.42  fof(c_0_33, plain, ![X27, X28, X29]:((((~v1_funct_2(X29,X27,X28)|X27=k1_relset_1(X27,X28,X29)|X28=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(X27!=k1_relset_1(X27,X28,X29)|v1_funct_2(X29,X27,X28)|X28=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))&((~v1_funct_2(X29,X27,X28)|X27=k1_relset_1(X27,X28,X29)|X27!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(X27!=k1_relset_1(X27,X28,X29)|v1_funct_2(X29,X27,X28)|X27!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))))&((~v1_funct_2(X29,X27,X28)|X29=k1_xboole_0|X27=k1_xboole_0|X28!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(X29!=k1_xboole_0|v1_funct_2(X29,X27,X28)|X27=k1_xboole_0|X28!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.42  cnf(c_0_34, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3)))), inference(rw,[status(thm)],[c_0_26, c_0_24])).
% 0.20/0.42  cnf(c_0_35, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.42  cnf(c_0_36, plain, (k2_relat_1(k2_zfmisc_1(X1,X2))=X2|X1=k1_xboole_0|X2=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.42  cnf(c_0_37, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.42  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.42  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.42  fof(c_0_40, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|k1_relset_1(X24,X25,X26)=k1_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.42  cnf(c_0_41, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.42  cnf(c_0_42, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_32])).
% 0.20/0.42  fof(c_0_43, plain, ![X23]:((k1_relat_1(X23)!=k1_xboole_0|X23=k1_xboole_0|~v1_relat_1(X23))&(k2_relat_1(X23)!=k1_xboole_0|X23=k1_xboole_0|~v1_relat_1(X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.20/0.42  fof(c_0_44, plain, ![X10]:(~r1_tarski(X10,k1_xboole_0)|X10=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.20/0.42  fof(c_0_45, plain, ![X15, X16]:r1_tarski(k1_relat_1(k2_zfmisc_1(X15,X16)),X15), inference(variable_rename,[status(thm)],[t193_relat_1])).
% 0.20/0.42  cnf(c_0_46, plain, (X1=k1_xboole_0|X2=k1_xboole_0|r1_tarski(k2_relat_1(X3),X2)|~v1_relat_1(X3)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.20/0.42  cnf(c_0_47, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.42  cnf(c_0_48, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_49, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.42  cnf(c_0_50, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk4_0)=esk2_0|k1_xboole_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_39]), c_0_42])])).
% 0.20/0.42  cnf(c_0_51, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.42  cnf(c_0_52, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.42  cnf(c_0_53, plain, (r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.42  cnf(c_0_54, negated_conjecture, (k1_relat_1(esk4_0)!=esk2_0|~r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_55, negated_conjecture, (k1_xboole_0=esk3_0|k1_xboole_0=esk2_0|r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.20/0.42  cnf(c_0_56, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0|k1_xboole_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_39])])).
% 0.20/0.42  cnf(c_0_57, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|k1_relat_1(k2_zfmisc_1(X1,X2))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_37])).
% 0.20/0.42  cnf(c_0_58, plain, (k1_relat_1(k2_zfmisc_1(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.42  cnf(c_0_59, negated_conjecture, (k1_xboole_0=esk2_0|k1_xboole_0=esk3_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.20/0.42  cnf(c_0_60, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.42  cnf(c_0_61, negated_conjecture, (k1_xboole_0=esk2_0|esk3_0!=esk2_0), inference(ef,[status(thm)],[c_0_59])).
% 0.20/0.42  fof(c_0_62, plain, ![X17, X18]:r1_tarski(k2_relat_1(k2_zfmisc_1(X17,X18)),X18), inference(variable_rename,[status(thm)],[t194_relat_1])).
% 0.20/0.42  cnf(c_0_63, negated_conjecture, (k2_zfmisc_1(esk2_0,X1)=esk2_0|esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.42  cnf(c_0_64, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_60])).
% 0.20/0.42  cnf(c_0_65, plain, (r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.42  cnf(c_0_66, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.42  cnf(c_0_67, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.42  cnf(c_0_68, negated_conjecture, (r1_tarski(esk4_0,esk2_0)|esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_47, c_0_63])).
% 0.20/0.42  cnf(c_0_69, negated_conjecture, (v1_relat_1(esk2_0)|esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_64, c_0_61])).
% 0.20/0.42  cnf(c_0_70, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.42  cnf(c_0_71, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.42  cnf(c_0_72, plain, (k2_relat_1(k2_zfmisc_1(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_65])).
% 0.20/0.42  cnf(c_0_73, plain, (r1_tarski(k2_relat_1(X1),k1_xboole_0)|~v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_66]), c_0_64])])).
% 0.20/0.42  fof(c_0_74, plain, ![X9]:r1_tarski(k1_xboole_0,X9), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.42  cnf(c_0_75, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),k1_relat_1(esk2_0))|esk3_0!=esk2_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_48])]), c_0_69])).
% 0.20/0.42  cnf(c_0_76, negated_conjecture, (k1_relat_1(esk2_0)=esk2_0|esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_70, c_0_61])).
% 0.20/0.42  cnf(c_0_77, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_37])])).
% 0.20/0.42  cnf(c_0_78, plain, (k2_relat_1(X1)=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_52, c_0_73])).
% 0.20/0.42  cnf(c_0_79, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.42  cnf(c_0_80, negated_conjecture, (X1=esk2_0|esk3_0!=esk2_0|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_52, c_0_61])).
% 0.20/0.42  cnf(c_0_81, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),esk2_0)|esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.42  cnf(c_0_82, negated_conjecture, (k2_zfmisc_1(X1,esk3_0)=esk3_0|k1_xboole_0=esk2_0), inference(spm,[status(thm)],[c_0_77, c_0_59])).
% 0.20/0.42  cnf(c_0_83, negated_conjecture, (k1_relat_1(esk4_0)!=esk2_0|~r1_tarski(esk4_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_78]), c_0_79]), c_0_48])])).
% 0.20/0.42  cnf(c_0_84, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0|esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.20/0.42  cnf(c_0_85, plain, (r1_tarski(k1_relat_1(k2_relat_1(X1)),k1_xboole_0)|~v1_relat_1(k2_relat_1(X1))|~v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_73]), c_0_70]), c_0_64])])).
% 0.20/0.42  cnf(c_0_86, negated_conjecture, (k2_relat_1(esk3_0)=esk3_0|k1_xboole_0=esk2_0), inference(spm,[status(thm)],[c_0_66, c_0_59])).
% 0.20/0.42  cnf(c_0_87, negated_conjecture, (k1_xboole_0=esk2_0|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_79, c_0_59])).
% 0.20/0.42  cnf(c_0_88, negated_conjecture, (k1_xboole_0=esk2_0|v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_64, c_0_59])).
% 0.20/0.42  cnf(c_0_89, negated_conjecture, (k1_xboole_0=esk4_0|k1_relat_1(esk4_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_48])).
% 0.20/0.42  cnf(c_0_90, negated_conjecture, (k1_xboole_0=esk2_0|X1=esk3_0|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_52, c_0_59])).
% 0.20/0.42  cnf(c_0_91, negated_conjecture, (k1_xboole_0=esk2_0|r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_47, c_0_82])).
% 0.20/0.42  cnf(c_0_92, negated_conjecture, (esk3_0!=esk2_0|~r1_tarski(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.20/0.42  cnf(c_0_93, negated_conjecture, (k1_xboole_0=esk2_0|r1_tarski(k1_relat_1(esk3_0),k1_xboole_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87]), c_0_88])).
% 0.20/0.42  cnf(c_0_94, negated_conjecture, (k1_xboole_0=esk3_0|k1_xboole_0=esk4_0|k1_xboole_0!=esk2_0), inference(spm,[status(thm)],[c_0_89, c_0_56])).
% 0.20/0.42  cnf(c_0_95, negated_conjecture, (esk3_0=esk4_0|k1_xboole_0=esk2_0), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.20/0.42  cnf(c_0_96, negated_conjecture, (esk3_0!=esk2_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_61]), c_0_68])).
% 0.20/0.42  cnf(c_0_97, negated_conjecture, (k1_relat_1(esk3_0)=k1_xboole_0|k1_xboole_0=esk2_0), inference(spm,[status(thm)],[c_0_52, c_0_93])).
% 0.20/0.42  cnf(c_0_98, negated_conjecture, (esk3_0=esk4_0|esk2_0=esk4_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96])).
% 0.20/0.42  cnf(c_0_99, negated_conjecture, (k1_xboole_0=esk3_0|~r1_tarski(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_83, c_0_56])).
% 0.20/0.42  fof(c_0_100, plain, ![X30, X31]:(v1_xboole_0(X30)|~v1_xboole_0(X31)|v1_xboole_0(k1_funct_2(X30,X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_funct_2])])])).
% 0.20/0.42  cnf(c_0_101, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|esk2_0=esk4_0|k1_xboole_0=esk2_0), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.20/0.42  cnf(c_0_102, negated_conjecture, (k2_zfmisc_1(esk2_0,X1)=esk2_0|esk3_0=esk4_0), inference(spm,[status(thm)],[c_0_60, c_0_95])).
% 0.20/0.42  cnf(c_0_103, negated_conjecture, (esk3_0=esk4_0|~r1_tarski(esk4_0,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_95]), c_0_96])).
% 0.20/0.42  cnf(c_0_104, plain, (v1_xboole_0(X1)|v1_xboole_0(k1_funct_2(X1,X2))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_100])).
% 0.20/0.42  fof(c_0_105, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.42  cnf(c_0_106, negated_conjecture, (k1_xboole_0=esk2_0|esk2_0=esk4_0|k1_xboole_0=esk4_0), inference(spm,[status(thm)],[c_0_89, c_0_101])).
% 0.20/0.42  cnf(c_0_107, negated_conjecture, (esk3_0=esk4_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_102]), c_0_103])).
% 0.20/0.42  fof(c_0_108, plain, ![X8]:(~v1_xboole_0(X8)|X8=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.42  cnf(c_0_109, plain, (v1_xboole_0(X1)|v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))|~v1_xboole_0(X2)), inference(rw,[status(thm)],[c_0_104, c_0_24])).
% 0.20/0.42  cnf(c_0_110, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.42  cnf(c_0_111, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_105])).
% 0.20/0.42  cnf(c_0_112, negated_conjecture, (k1_xboole_0=esk4_0|esk2_0=esk4_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_106]), c_0_96])).
% 0.20/0.42  cnf(c_0_113, negated_conjecture, (esk2_0!=esk4_0), inference(rw,[status(thm)],[c_0_96, c_0_107])).
% 0.20/0.42  cnf(c_0_114, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_108])).
% 0.20/0.42  cnf(c_0_115, plain, (v1_xboole_0(k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0)))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 0.20/0.42  cnf(c_0_116, negated_conjecture, (~v1_xboole_0(k5_partfun1(esk2_0,esk3_0,k3_partfun1(k1_xboole_0,esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_111, c_0_32])).
% 0.20/0.42  cnf(c_0_117, negated_conjecture, (k1_xboole_0=esk4_0), inference(sr,[status(thm)],[c_0_112, c_0_113])).
% 0.20/0.42  cnf(c_0_118, plain, (k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0))=k1_xboole_0|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_114, c_0_115])).
% 0.20/0.42  cnf(c_0_119, negated_conjecture, (esk2_0=esk4_0|v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_110, c_0_112])).
% 0.20/0.42  cnf(c_0_120, negated_conjecture, (~v1_xboole_0(k5_partfun1(esk2_0,esk4_0,k3_partfun1(esk4_0,esk2_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_107]), c_0_107]), c_0_117])).
% 0.20/0.42  cnf(c_0_121, plain, (k5_partfun1(X1,esk4_0,k3_partfun1(esk4_0,X1,esk4_0))=esk4_0|v1_xboole_0(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118, c_0_117]), c_0_117]), c_0_117]), c_0_117])).
% 0.20/0.42  cnf(c_0_122, negated_conjecture, (v1_xboole_0(esk4_0)), inference(sr,[status(thm)],[c_0_119, c_0_113])).
% 0.20/0.42  cnf(c_0_123, plain, (X1=esk4_0|~v1_xboole_0(X1)), inference(rw,[status(thm)],[c_0_114, c_0_117])).
% 0.20/0.42  cnf(c_0_124, negated_conjecture, (v1_xboole_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_122])])).
% 0.20/0.42  cnf(c_0_125, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_124]), c_0_113]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 126
% 0.20/0.42  # Proof object clause steps            : 89
% 0.20/0.42  # Proof object formula steps           : 37
% 0.20/0.42  # Proof object conjectures             : 53
% 0.20/0.42  # Proof object clause conjectures      : 50
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 25
% 0.20/0.42  # Proof object initial formulas used   : 19
% 0.20/0.42  # Proof object generating inferences   : 54
% 0.20/0.42  # Proof object simplifying inferences  : 47
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 19
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 35
% 0.20/0.42  # Removed in clause preprocessing      : 1
% 0.20/0.42  # Initial clauses in saturation        : 34
% 0.20/0.42  # Processed clauses                    : 623
% 0.20/0.42  # ...of these trivial                  : 45
% 0.20/0.42  # ...subsumed                          : 281
% 0.20/0.42  # ...remaining for further processing  : 297
% 0.20/0.42  # Other redundant clauses eliminated   : 10
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 24
% 0.20/0.42  # Backward-rewritten                   : 164
% 0.20/0.42  # Generated clauses                    : 1498
% 0.20/0.42  # ...of the previous two non-trivial   : 1400
% 0.20/0.42  # Contextual simplify-reflections      : 10
% 0.20/0.42  # Paramodulations                      : 1477
% 0.20/0.42  # Factorizations                       : 4
% 0.20/0.42  # Equation resolutions                 : 10
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 63
% 0.20/0.42  #    Positive orientable unit clauses  : 17
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 2
% 0.20/0.42  #    Non-unit-clauses                  : 44
% 0.20/0.42  # Current number of unprocessed clauses: 394
% 0.20/0.42  # ...number of literals in the above   : 1814
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 231
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 4836
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 2305
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 245
% 0.20/0.42  # Unit Clause-clause subsumption calls : 180
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 7
% 0.20/0.42  # BW rewrite match successes           : 7
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 22069
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.066 s
% 0.20/0.42  # System time              : 0.007 s
% 0.20/0.42  # Total time               : 0.073 s
% 0.20/0.42  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
