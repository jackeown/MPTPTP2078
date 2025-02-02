%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:15 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  135 (105959 expanded)
%              Number of clauses        :  100 (48048 expanded)
%              Number of leaves         :   18 (26125 expanded)
%              Depth                    :   23
%              Number of atoms          :  345 (306005 expanded)
%              Number of equality atoms :  154 (100307 expanded)
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

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

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

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X3,k1_funct_2(X1,X2))
         => ( k1_relat_1(X3) = X1
            & r1_tarski(k2_relat_1(X3),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t169_funct_2])).

fof(c_0_19,plain,(
    ! [X32,X33,X34] :
      ( ( v1_funct_1(X34)
        | ~ r2_hidden(X34,k1_funct_2(X32,X33)) )
      & ( v1_funct_2(X34,X32,X33)
        | ~ r2_hidden(X34,k1_funct_2(X32,X33)) )
      & ( m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
        | ~ r2_hidden(X34,k1_funct_2(X32,X33)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_2])])])).

fof(c_0_20,plain,(
    ! [X35,X36] : k5_partfun1(X35,X36,k3_partfun1(k1_xboole_0,X35,X36)) = k1_funct_2(X35,X36) ),
    inference(variable_rename,[status(thm)],[t160_funct_2])).

fof(c_0_21,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & r2_hidden(esk4_0,k1_funct_2(esk2_0,esk3_0))
    & ( k1_relat_1(esk4_0) != esk2_0
      | ~ r1_tarski(k2_relat_1(esk4_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_22,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_23,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k2_xboole_0(X11,X12) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_24,plain,(
    ! [X22,X23] :
      ( ( r1_tarski(k1_relat_1(X22),k1_relat_1(X23))
        | ~ r1_tarski(X22,X23)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22) )
      & ( r1_tarski(k2_relat_1(X22),k2_relat_1(X23))
        | ~ r1_tarski(X22,X23)
        | ~ v1_relat_1(X23)
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_25,plain,(
    ! [X20,X21] :
      ( ( k1_relat_1(k2_zfmisc_1(X20,X21)) = X20
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0 )
      & ( k2_relat_1(k2_zfmisc_1(X20,X21)) = X21
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).

fof(c_0_26,plain,(
    ! [X18,X19] : v1_relat_1(k2_zfmisc_1(X18,X19)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)) = k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk4_0,k1_funct_2(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_36,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_37,plain,(
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

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk4_0,k5_partfun1(esk2_0,esk3_0,k3_partfun1(k1_xboole_0,esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_40,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r1_tarski(k2_relat_1(X3),X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_44,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | k1_relset_1(X24,X25,X26) = k1_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_45,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_48,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_41])).

fof(c_0_49,plain,(
    ! [X14,X15] :
      ( ( k2_zfmisc_1(X14,X15) != k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0 )
      & ( X14 != k1_xboole_0
        | k2_zfmisc_1(X14,X15) = k1_xboole_0 )
      & ( X15 != k1_xboole_0
        | k2_zfmisc_1(X14,X15) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r1_tarski(k2_relat_1(X3),X1)
    | ~ v1_relat_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_52,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk4_0) = esk2_0
    | k1_xboole_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_54,plain,
    ( X1 = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_43])).

cnf(c_0_55,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( k1_relat_1(esk4_0) != esk2_0
    | ~ r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | k1_xboole_0 = esk3_0
    | r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_46]),c_0_51])])).

cnf(c_0_58,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0
    | k1_xboole_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_46])])).

fof(c_0_59,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_60,plain,
    ( X1 = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_43])).

cnf(c_0_61,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | k1_xboole_0 = esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_65,plain,
    ( k2_relat_1(X1) = k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X2),k2_relat_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_33])).

cnf(c_0_66,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = esk4_0
    | ~ m1_subset_1(k2_zfmisc_1(esk2_0,esk3_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_46])).

cnf(c_0_67,negated_conjecture,
    ( k2_zfmisc_1(X1,esk3_0) = esk3_0
    | k1_xboole_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,plain,
    ( k2_relat_1(X1) = k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_33])).

cnf(c_0_70,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_71,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | esk3_0 = esk4_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_62])).

cnf(c_0_73,plain,
    ( k2_relat_1(X1) = k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_43])).

cnf(c_0_74,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( esk3_0 = esk4_0
    | k1_xboole_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_77,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | esk3_0 != esk2_0 ),
    inference(ef,[status(thm)],[c_0_62])).

cnf(c_0_78,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_79,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(esk2_0,esk3_0)) = k2_relat_1(esk4_0)
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_46]),c_0_35]),c_0_51])])).

cnf(c_0_80,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,X1) = esk2_0
    | esk3_0 = esk4_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( esk3_0 = esk4_0
    | r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_75])).

cnf(c_0_82,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_43])).

cnf(c_0_83,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,X1) = esk2_0
    | esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_77])).

cnf(c_0_85,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_61])).

cnf(c_0_86,negated_conjecture,
    ( k2_relat_1(esk2_0) = esk2_0
    | esk3_0 = esk4_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_75])).

cnf(c_0_87,negated_conjecture,
    ( k2_relat_1(esk2_0) = k2_relat_1(esk4_0)
    | esk3_0 = esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),k1_relat_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_46]),c_0_35]),c_0_51])])).

cnf(c_0_89,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_90,negated_conjecture,
    ( k2_relat_1(esk2_0) = esk2_0
    | esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_77])).

cnf(c_0_91,negated_conjecture,
    ( k2_relat_1(esk2_0) = k2_relat_1(esk4_0)
    | esk3_0 != esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_83]),c_0_84])).

cnf(c_0_92,plain,
    ( r1_tarski(k2_relat_1(X1),k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_78]),c_0_85])])).

cnf(c_0_93,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk2_0
    | esk3_0 = esk4_0 ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_94,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_64])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),k1_relat_1(esk2_0))
    | esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_83])).

cnf(c_0_96,negated_conjecture,
    ( k1_relat_1(esk2_0) = esk2_0
    | esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_89,c_0_77])).

cnf(c_0_97,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk2_0
    | esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_98,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_92]),c_0_64])])).

cnf(c_0_99,negated_conjecture,
    ( esk3_0 = esk4_0
    | k1_relat_1(esk4_0) != esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_93]),c_0_81])).

cnf(c_0_100,negated_conjecture,
    ( esk2_0 = X1
    | esk3_0 != esk2_0
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_77])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),esk2_0)
    | esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_102,negated_conjecture,
    ( k1_relat_1(esk4_0) != esk2_0
    | esk3_0 != esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_97]),c_0_84])).

cnf(c_0_103,negated_conjecture,
    ( k2_relat_1(esk4_0) = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_79]),c_0_35])])).

cnf(c_0_104,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | esk3_0 = esk4_0 ),
    inference(spm,[status(thm)],[c_0_99,c_0_58])).

cnf(c_0_105,negated_conjecture,
    ( esk3_0 != esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102])).

fof(c_0_106,plain,(
    ! [X30,X31] :
      ( v1_xboole_0(X30)
      | ~ v1_xboole_0(X31)
      | v1_xboole_0(k1_funct_2(X30,X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_funct_2])])])).

fof(c_0_107,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_108,negated_conjecture,
    ( k1_relat_1(esk4_0) != esk2_0
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_103]),c_0_64])])).

cnf(c_0_109,negated_conjecture,
    ( esk3_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_104]),c_0_105])).

cnf(c_0_110,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(k1_funct_2(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_111,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_112,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_58])).

cnf(c_0_113,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | k1_xboole_0 = esk4_0 ),
    inference(rw,[status(thm)],[c_0_62,c_0_109])).

fof(c_0_114,plain,(
    ! [X10] :
      ( ~ v1_xboole_0(X10)
      | X10 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_115,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | ~ v1_xboole_0(X2) ),
    inference(rw,[status(thm)],[c_0_110,c_0_28])).

cnf(c_0_116,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_117,negated_conjecture,
    ( ~ v1_xboole_0(k5_partfun1(esk2_0,esk3_0,k3_partfun1(k1_xboole_0,esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_111,c_0_39])).

cnf(c_0_118,negated_conjecture,
    ( k1_xboole_0 = esk4_0
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk4_0),k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk4_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_109]),c_0_109]),c_0_109])).

cnf(c_0_119,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,X1) = esk2_0
    | k1_xboole_0 = esk4_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_113])).

cnf(c_0_120,negated_conjecture,
    ( k1_xboole_0 = esk4_0
    | r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_113])).

cnf(c_0_121,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_114])).

cnf(c_0_122,plain,
    ( v1_xboole_0(k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0)))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_123,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_62])).

cnf(c_0_124,negated_conjecture,
    ( ~ v1_xboole_0(k5_partfun1(esk2_0,esk4_0,k3_partfun1(k1_xboole_0,esk2_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_109]),c_0_109])).

cnf(c_0_125,negated_conjecture,
    ( k1_xboole_0 = esk4_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_120]),c_0_120])).

cnf(c_0_126,plain,
    ( k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0)) = k1_xboole_0
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_127,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | v1_xboole_0(esk4_0) ),
    inference(rw,[status(thm)],[c_0_123,c_0_109])).

cnf(c_0_128,negated_conjecture,
    ( esk2_0 != esk4_0 ),
    inference(rw,[status(thm)],[c_0_105,c_0_109])).

cnf(c_0_129,negated_conjecture,
    ( ~ v1_xboole_0(k5_partfun1(esk2_0,esk4_0,k3_partfun1(esk4_0,esk2_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_130,plain,
    ( k5_partfun1(X1,esk4_0,k3_partfun1(esk4_0,X1,esk4_0)) = esk4_0
    | v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126,c_0_125]),c_0_125]),c_0_125]),c_0_125])).

cnf(c_0_131,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_127,c_0_125]),c_0_128])).

cnf(c_0_132,plain,
    ( X1 = esk4_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[c_0_121,c_0_125])).

cnf(c_0_133,negated_conjecture,
    ( v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_131])])).

cnf(c_0_134,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_128]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:18:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.50  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.50  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.50  #
% 0.20/0.50  # Preprocessing time       : 0.028 s
% 0.20/0.50  # Presaturation interreduction done
% 0.20/0.50  
% 0.20/0.50  # Proof found!
% 0.20/0.50  # SZS status Theorem
% 0.20/0.50  # SZS output start CNFRefutation
% 0.20/0.50  fof(t169_funct_2, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X3,k1_funct_2(X1,X2))=>(k1_relat_1(X3)=X1&r1_tarski(k2_relat_1(X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_funct_2)).
% 0.20/0.50  fof(t121_funct_2, axiom, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 0.20/0.50  fof(t160_funct_2, axiom, ![X1, X2]:k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))=k1_funct_2(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_funct_2)).
% 0.20/0.50  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.50  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.50  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.20/0.50  fof(t195_relat_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((k1_relat_1(k2_zfmisc_1(X1,X2))=X1&k2_relat_1(k2_zfmisc_1(X1,X2))=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 0.20/0.50  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.50  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.50  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.50  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.50  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.50  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.50  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.20/0.50  fof(fc3_funct_2, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&v1_xboole_0(X2))=>v1_xboole_0(k1_funct_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_2)).
% 0.20/0.50  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.50  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.50  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.50  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X3,k1_funct_2(X1,X2))=>(k1_relat_1(X3)=X1&r1_tarski(k2_relat_1(X3),X2))))), inference(assume_negation,[status(cth)],[t169_funct_2])).
% 0.20/0.50  fof(c_0_19, plain, ![X32, X33, X34]:(((v1_funct_1(X34)|~r2_hidden(X34,k1_funct_2(X32,X33)))&(v1_funct_2(X34,X32,X33)|~r2_hidden(X34,k1_funct_2(X32,X33))))&(m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|~r2_hidden(X34,k1_funct_2(X32,X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_2])])])).
% 0.20/0.50  fof(c_0_20, plain, ![X35, X36]:k5_partfun1(X35,X36,k3_partfun1(k1_xboole_0,X35,X36))=k1_funct_2(X35,X36), inference(variable_rename,[status(thm)],[t160_funct_2])).
% 0.20/0.50  fof(c_0_21, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&(r2_hidden(esk4_0,k1_funct_2(esk2_0,esk3_0))&(k1_relat_1(esk4_0)!=esk2_0|~r1_tarski(k2_relat_1(esk4_0),esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.20/0.50  fof(c_0_22, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.50  fof(c_0_23, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k2_xboole_0(X11,X12)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.50  fof(c_0_24, plain, ![X22, X23]:((r1_tarski(k1_relat_1(X22),k1_relat_1(X23))|~r1_tarski(X22,X23)|~v1_relat_1(X23)|~v1_relat_1(X22))&(r1_tarski(k2_relat_1(X22),k2_relat_1(X23))|~r1_tarski(X22,X23)|~v1_relat_1(X23)|~v1_relat_1(X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.20/0.50  fof(c_0_25, plain, ![X20, X21]:((k1_relat_1(k2_zfmisc_1(X20,X21))=X20|(X20=k1_xboole_0|X21=k1_xboole_0))&(k2_relat_1(k2_zfmisc_1(X20,X21))=X21|(X20=k1_xboole_0|X21=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).
% 0.20/0.50  fof(c_0_26, plain, ![X18, X19]:v1_relat_1(k2_zfmisc_1(X18,X19)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.50  cnf(c_0_27, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.50  cnf(c_0_28, plain, (k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.50  cnf(c_0_29, negated_conjecture, (r2_hidden(esk4_0,k1_funct_2(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.50  cnf(c_0_30, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.50  cnf(c_0_31, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.50  cnf(c_0_32, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.50  cnf(c_0_33, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.50  cnf(c_0_34, plain, (k2_relat_1(k2_zfmisc_1(X1,X2))=X2|X1=k1_xboole_0|X2=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.50  cnf(c_0_35, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.50  fof(c_0_36, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.50  fof(c_0_37, plain, ![X27, X28, X29]:((((~v1_funct_2(X29,X27,X28)|X27=k1_relset_1(X27,X28,X29)|X28=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(X27!=k1_relset_1(X27,X28,X29)|v1_funct_2(X29,X27,X28)|X28=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))&((~v1_funct_2(X29,X27,X28)|X27=k1_relset_1(X27,X28,X29)|X27!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(X27!=k1_relset_1(X27,X28,X29)|v1_funct_2(X29,X27,X28)|X27!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))))&((~v1_funct_2(X29,X27,X28)|X29=k1_xboole_0|X27=k1_xboole_0|X28!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(X29!=k1_xboole_0|v1_funct_2(X29,X27,X28)|X27=k1_xboole_0|X28!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.50  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3)))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.50  cnf(c_0_39, negated_conjecture, (r2_hidden(esk4_0,k5_partfun1(esk2_0,esk3_0,k3_partfun1(k1_xboole_0,esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_29, c_0_28])).
% 0.20/0.50  cnf(c_0_40, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3)))), inference(rw,[status(thm)],[c_0_30, c_0_28])).
% 0.20/0.50  cnf(c_0_41, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.50  cnf(c_0_42, plain, (X1=k1_xboole_0|X2=k1_xboole_0|r1_tarski(k2_relat_1(X3),X2)|~v1_relat_1(X3)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.20/0.50  cnf(c_0_43, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.50  fof(c_0_44, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|k1_relset_1(X24,X25,X26)=k1_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.50  cnf(c_0_45, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.50  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.50  cnf(c_0_47, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_40, c_0_39])).
% 0.20/0.50  cnf(c_0_48, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_32, c_0_41])).
% 0.20/0.50  fof(c_0_49, plain, ![X14, X15]:((k2_zfmisc_1(X14,X15)!=k1_xboole_0|(X14=k1_xboole_0|X15=k1_xboole_0))&((X14!=k1_xboole_0|k2_zfmisc_1(X14,X15)=k1_xboole_0)&(X15!=k1_xboole_0|k2_zfmisc_1(X14,X15)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.50  cnf(c_0_50, plain, (X1=k1_xboole_0|X2=k1_xboole_0|r1_tarski(k2_relat_1(X3),X1)|~v1_relat_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.50  cnf(c_0_51, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.50  cnf(c_0_52, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.50  cnf(c_0_53, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk4_0)=esk2_0|k1_xboole_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.20/0.50  cnf(c_0_54, plain, (X1=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_48, c_0_43])).
% 0.20/0.50  cnf(c_0_55, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.50  cnf(c_0_56, negated_conjecture, (k1_relat_1(esk4_0)!=esk2_0|~r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.50  cnf(c_0_57, negated_conjecture, (k1_xboole_0=esk2_0|k1_xboole_0=esk3_0|r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_46]), c_0_51])])).
% 0.20/0.50  cnf(c_0_58, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0|k1_xboole_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_46])])).
% 0.20/0.50  fof(c_0_59, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.50  cnf(c_0_60, plain, (X1=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_54, c_0_43])).
% 0.20/0.50  cnf(c_0_61, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_55])).
% 0.20/0.50  cnf(c_0_62, negated_conjecture, (k1_xboole_0=esk3_0|k1_xboole_0=esk2_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.20/0.50  cnf(c_0_63, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.50  cnf(c_0_64, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.50  cnf(c_0_65, plain, (k2_relat_1(X1)=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X2),k2_relat_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_48, c_0_33])).
% 0.20/0.50  cnf(c_0_66, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=esk4_0|~m1_subset_1(k2_zfmisc_1(esk2_0,esk3_0),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_60, c_0_46])).
% 0.20/0.50  cnf(c_0_67, negated_conjecture, (k2_zfmisc_1(X1,esk3_0)=esk3_0|k1_xboole_0=esk2_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.50  cnf(c_0_68, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.50  cnf(c_0_69, plain, (k2_relat_1(X1)=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_65, c_0_33])).
% 0.20/0.50  cnf(c_0_70, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.50  cnf(c_0_71, negated_conjecture, (k1_xboole_0=esk2_0|esk3_0=esk4_0|~m1_subset_1(esk3_0,k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.50  cnf(c_0_72, negated_conjecture, (k1_xboole_0=esk2_0|m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_68, c_0_62])).
% 0.20/0.50  cnf(c_0_73, plain, (k2_relat_1(X1)=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_69, c_0_43])).
% 0.20/0.50  cnf(c_0_74, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_70])).
% 0.20/0.50  cnf(c_0_75, negated_conjecture, (esk3_0=esk4_0|k1_xboole_0=esk2_0), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.50  cnf(c_0_76, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.50  cnf(c_0_77, negated_conjecture, (k1_xboole_0=esk2_0|esk3_0!=esk2_0), inference(ef,[status(thm)],[c_0_62])).
% 0.20/0.50  cnf(c_0_78, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.50  cnf(c_0_79, negated_conjecture, (k2_relat_1(k2_zfmisc_1(esk2_0,esk3_0))=k2_relat_1(esk4_0)|~r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_46]), c_0_35]), c_0_51])])).
% 0.20/0.50  cnf(c_0_80, negated_conjecture, (k2_zfmisc_1(esk2_0,X1)=esk2_0|esk3_0=esk4_0), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.50  cnf(c_0_81, negated_conjecture, (esk3_0=esk4_0|r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_64, c_0_75])).
% 0.20/0.50  cnf(c_0_82, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_76, c_0_43])).
% 0.20/0.50  cnf(c_0_83, negated_conjecture, (k2_zfmisc_1(esk2_0,X1)=esk2_0|esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_74, c_0_77])).
% 0.20/0.50  cnf(c_0_84, negated_conjecture, (r1_tarski(esk2_0,X1)|esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_64, c_0_77])).
% 0.20/0.50  cnf(c_0_85, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_35, c_0_61])).
% 0.20/0.50  cnf(c_0_86, negated_conjecture, (k2_relat_1(esk2_0)=esk2_0|esk3_0=esk4_0), inference(spm,[status(thm)],[c_0_78, c_0_75])).
% 0.20/0.50  cnf(c_0_87, negated_conjecture, (k2_relat_1(esk2_0)=k2_relat_1(esk4_0)|esk3_0=esk4_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])).
% 0.20/0.50  cnf(c_0_88, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),k1_relat_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_46]), c_0_35]), c_0_51])])).
% 0.20/0.50  cnf(c_0_89, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.50  cnf(c_0_90, negated_conjecture, (k2_relat_1(esk2_0)=esk2_0|esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_78, c_0_77])).
% 0.20/0.50  cnf(c_0_91, negated_conjecture, (k2_relat_1(esk2_0)=k2_relat_1(esk4_0)|esk3_0!=esk2_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_83]), c_0_84])).
% 0.20/0.50  cnf(c_0_92, plain, (r1_tarski(k2_relat_1(X1),k1_xboole_0)|~v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_78]), c_0_85])])).
% 0.20/0.50  cnf(c_0_93, negated_conjecture, (k2_relat_1(esk4_0)=esk2_0|esk3_0=esk4_0), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.20/0.50  cnf(c_0_94, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_48, c_0_64])).
% 0.20/0.50  cnf(c_0_95, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),k1_relat_1(esk2_0))|esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_88, c_0_83])).
% 0.20/0.50  cnf(c_0_96, negated_conjecture, (k1_relat_1(esk2_0)=esk2_0|esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_89, c_0_77])).
% 0.20/0.50  cnf(c_0_97, negated_conjecture, (k2_relat_1(esk4_0)=esk2_0|esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.20/0.50  cnf(c_0_98, plain, (k2_relat_1(X1)=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_92]), c_0_64])])).
% 0.20/0.50  cnf(c_0_99, negated_conjecture, (esk3_0=esk4_0|k1_relat_1(esk4_0)!=esk2_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_93]), c_0_81])).
% 0.20/0.50  cnf(c_0_100, negated_conjecture, (esk2_0=X1|esk3_0!=esk2_0|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_94, c_0_77])).
% 0.20/0.50  cnf(c_0_101, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),esk2_0)|esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.20/0.50  cnf(c_0_102, negated_conjecture, (k1_relat_1(esk4_0)!=esk2_0|esk3_0!=esk2_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_97]), c_0_84])).
% 0.20/0.50  cnf(c_0_103, negated_conjecture, (k2_relat_1(esk4_0)=k1_xboole_0|~r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k1_xboole_0)|~r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_79]), c_0_35])])).
% 0.20/0.50  cnf(c_0_104, negated_conjecture, (k1_xboole_0=esk3_0|esk3_0=esk4_0), inference(spm,[status(thm)],[c_0_99, c_0_58])).
% 0.20/0.50  cnf(c_0_105, negated_conjecture, (esk3_0!=esk2_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_102])).
% 0.20/0.50  fof(c_0_106, plain, ![X30, X31]:(v1_xboole_0(X30)|~v1_xboole_0(X31)|v1_xboole_0(k1_funct_2(X30,X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_funct_2])])])).
% 0.20/0.50  fof(c_0_107, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.50  cnf(c_0_108, negated_conjecture, (k1_relat_1(esk4_0)!=esk2_0|~r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k1_xboole_0)|~r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_103]), c_0_64])])).
% 0.20/0.50  cnf(c_0_109, negated_conjecture, (esk3_0=esk4_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_104]), c_0_105])).
% 0.20/0.50  cnf(c_0_110, plain, (v1_xboole_0(X1)|v1_xboole_0(k1_funct_2(X1,X2))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_106])).
% 0.20/0.50  cnf(c_0_111, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_107])).
% 0.20/0.50  cnf(c_0_112, negated_conjecture, (k1_xboole_0=esk3_0|~r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k1_xboole_0)|~r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_108, c_0_58])).
% 0.20/0.50  cnf(c_0_113, negated_conjecture, (k1_xboole_0=esk2_0|k1_xboole_0=esk4_0), inference(rw,[status(thm)],[c_0_62, c_0_109])).
% 0.20/0.50  fof(c_0_114, plain, ![X10]:(~v1_xboole_0(X10)|X10=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.50  cnf(c_0_115, plain, (v1_xboole_0(X1)|v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))|~v1_xboole_0(X2)), inference(rw,[status(thm)],[c_0_110, c_0_28])).
% 0.20/0.50  cnf(c_0_116, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.50  cnf(c_0_117, negated_conjecture, (~v1_xboole_0(k5_partfun1(esk2_0,esk3_0,k3_partfun1(k1_xboole_0,esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_111, c_0_39])).
% 0.20/0.50  cnf(c_0_118, negated_conjecture, (k1_xboole_0=esk4_0|~r1_tarski(k2_zfmisc_1(esk2_0,esk4_0),k1_xboole_0)|~r1_tarski(k2_zfmisc_1(esk2_0,esk4_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_109]), c_0_109]), c_0_109])).
% 0.20/0.50  cnf(c_0_119, negated_conjecture, (k2_zfmisc_1(esk2_0,X1)=esk2_0|k1_xboole_0=esk4_0), inference(spm,[status(thm)],[c_0_74, c_0_113])).
% 0.20/0.50  cnf(c_0_120, negated_conjecture, (k1_xboole_0=esk4_0|r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_64, c_0_113])).
% 0.20/0.50  cnf(c_0_121, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_114])).
% 0.20/0.50  cnf(c_0_122, plain, (v1_xboole_0(k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0)))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_115, c_0_116])).
% 0.20/0.50  cnf(c_0_123, negated_conjecture, (k1_xboole_0=esk2_0|v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_116, c_0_62])).
% 0.20/0.50  cnf(c_0_124, negated_conjecture, (~v1_xboole_0(k5_partfun1(esk2_0,esk4_0,k3_partfun1(k1_xboole_0,esk2_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_109]), c_0_109])).
% 0.20/0.50  cnf(c_0_125, negated_conjecture, (k1_xboole_0=esk4_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_120]), c_0_120])).
% 0.20/0.50  cnf(c_0_126, plain, (k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0))=k1_xboole_0|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 0.20/0.50  cnf(c_0_127, negated_conjecture, (k1_xboole_0=esk2_0|v1_xboole_0(esk4_0)), inference(rw,[status(thm)],[c_0_123, c_0_109])).
% 0.20/0.50  cnf(c_0_128, negated_conjecture, (esk2_0!=esk4_0), inference(rw,[status(thm)],[c_0_105, c_0_109])).
% 0.20/0.50  cnf(c_0_129, negated_conjecture, (~v1_xboole_0(k5_partfun1(esk2_0,esk4_0,k3_partfun1(esk4_0,esk2_0,esk4_0)))), inference(rw,[status(thm)],[c_0_124, c_0_125])).
% 0.20/0.50  cnf(c_0_130, plain, (k5_partfun1(X1,esk4_0,k3_partfun1(esk4_0,X1,esk4_0))=esk4_0|v1_xboole_0(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126, c_0_125]), c_0_125]), c_0_125]), c_0_125])).
% 0.20/0.50  cnf(c_0_131, negated_conjecture, (v1_xboole_0(esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_127, c_0_125]), c_0_128])).
% 0.20/0.50  cnf(c_0_132, plain, (X1=esk4_0|~v1_xboole_0(X1)), inference(rw,[status(thm)],[c_0_121, c_0_125])).
% 0.20/0.50  cnf(c_0_133, negated_conjecture, (v1_xboole_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_131])])).
% 0.20/0.50  cnf(c_0_134, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_133]), c_0_128]), ['proof']).
% 0.20/0.50  # SZS output end CNFRefutation
% 0.20/0.50  # Proof object total steps             : 135
% 0.20/0.50  # Proof object clause steps            : 100
% 0.20/0.50  # Proof object formula steps           : 35
% 0.20/0.50  # Proof object conjectures             : 57
% 0.20/0.50  # Proof object clause conjectures      : 54
% 0.20/0.50  # Proof object formula conjectures     : 3
% 0.20/0.50  # Proof object initial clauses used    : 25
% 0.20/0.50  # Proof object initial formulas used   : 18
% 0.20/0.50  # Proof object generating inferences   : 60
% 0.20/0.50  # Proof object simplifying inferences  : 56
% 0.20/0.50  # Training examples: 0 positive, 0 negative
% 0.20/0.50  # Parsed axioms                        : 18
% 0.20/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.50  # Initial clauses                      : 35
% 0.20/0.50  # Removed in clause preprocessing      : 1
% 0.20/0.50  # Initial clauses in saturation        : 34
% 0.20/0.50  # Processed clauses                    : 1097
% 0.20/0.50  # ...of these trivial                  : 70
% 0.20/0.50  # ...subsumed                          : 526
% 0.20/0.50  # ...remaining for further processing  : 501
% 0.20/0.50  # Other redundant clauses eliminated   : 8
% 0.20/0.50  # Clauses deleted for lack of memory   : 0
% 0.20/0.50  # Backward-subsumed                    : 32
% 0.20/0.50  # Backward-rewritten                   : 365
% 0.20/0.50  # Generated clauses                    : 3950
% 0.20/0.50  # ...of the previous two non-trivial   : 3374
% 0.20/0.50  # Contextual simplify-reflections      : 30
% 0.20/0.50  # Paramodulations                      : 3941
% 0.20/0.50  # Factorizations                       : 2
% 0.20/0.50  # Equation resolutions                 : 8
% 0.20/0.50  # Propositional unsat checks           : 0
% 0.20/0.50  #    Propositional check models        : 0
% 0.20/0.50  #    Propositional check unsatisfiable : 0
% 0.20/0.50  #    Propositional clauses             : 0
% 0.20/0.50  #    Propositional clauses after purity: 0
% 0.20/0.50  #    Propositional unsat core size     : 0
% 0.20/0.50  #    Propositional preprocessing time  : 0.000
% 0.20/0.50  #    Propositional encoding time       : 0.000
% 0.20/0.50  #    Propositional solver time         : 0.000
% 0.20/0.50  #    Success case prop preproc time    : 0.000
% 0.20/0.50  #    Success case prop encoding time   : 0.000
% 0.20/0.50  #    Success case prop solver time     : 0.000
% 0.20/0.50  # Current number of processed clauses  : 64
% 0.20/0.50  #    Positive orientable unit clauses  : 16
% 0.20/0.50  #    Positive unorientable unit clauses: 1
% 0.20/0.50  #    Negative unit clauses             : 2
% 0.20/0.50  #    Non-unit-clauses                  : 45
% 0.20/0.50  # Current number of unprocessed clauses: 1691
% 0.20/0.50  # ...number of literals in the above   : 10766
% 0.20/0.50  # Current number of archived formulas  : 0
% 0.20/0.50  # Current number of archived clauses   : 432
% 0.20/0.50  # Clause-clause subsumption calls (NU) : 36506
% 0.20/0.50  # Rec. Clause-clause subsumption calls : 7251
% 0.20/0.50  # Non-unit clause-clause subsumptions  : 504
% 0.20/0.50  # Unit Clause-clause subsumption calls : 231
% 0.20/0.50  # Rewrite failures with RHS unbound    : 0
% 0.20/0.50  # BW rewrite match attempts            : 10
% 0.20/0.50  # BW rewrite match successes           : 9
% 0.20/0.50  # Condensation attempts                : 0
% 0.20/0.50  # Condensation successes               : 0
% 0.20/0.50  # Termbank termtop insertions          : 92458
% 0.20/0.50  
% 0.20/0.50  # -------------------------------------------------
% 0.20/0.50  # User time                : 0.153 s
% 0.20/0.50  # System time              : 0.005 s
% 0.20/0.50  # Total time               : 0.158 s
% 0.20/0.50  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
