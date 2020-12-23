%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:56 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 261 expanded)
%              Number of clauses        :   37 ( 101 expanded)
%              Number of leaves         :    9 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :  232 (1378 expanded)
%              Number of equality atoms :   52 ( 223 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( X2 != k1_xboole_0
       => ! [X5] :
            ( r2_hidden(X5,k8_relset_1(X1,X2,X4,X3))
          <=> ( r2_hidden(X5,X1)
              & r2_hidden(k1_funct_1(X4,X5),X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_2)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( X2 != k1_xboole_0
         => ! [X5] :
              ( r2_hidden(X5,k8_relset_1(X1,X2,X4,X3))
            <=> ( r2_hidden(X5,X1)
                & r2_hidden(k1_funct_1(X4,X5),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t46_funct_2])).

fof(c_0_10,plain,(
    ! [X27,X28,X29] :
      ( ( r2_hidden(X27,k1_relat_1(X29))
        | ~ r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( X28 = k1_funct_1(X29,X27)
        | ~ r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( ~ r2_hidden(X27,k1_relat_1(X29))
        | X28 != k1_funct_1(X29,X27)
        | r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_11,plain,(
    ! [X22,X23,X24,X26] :
      ( ( r2_hidden(esk4_3(X22,X23,X24),k2_relat_1(X24))
        | ~ r2_hidden(X22,k10_relat_1(X24,X23))
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(k4_tarski(X22,esk4_3(X22,X23,X24)),X24)
        | ~ r2_hidden(X22,k10_relat_1(X24,X23))
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(esk4_3(X22,X23,X24),X23)
        | ~ r2_hidden(X22,k10_relat_1(X24,X23))
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(X26,k2_relat_1(X24))
        | ~ r2_hidden(k4_tarski(X22,X26),X24)
        | ~ r2_hidden(X26,X23)
        | r2_hidden(X22,k10_relat_1(X24,X23))
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

fof(c_0_12,negated_conjecture,
    ( v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,esk5_0,esk6_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    & esk6_0 != k1_xboole_0
    & ( ~ r2_hidden(esk9_0,k8_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))
      | ~ r2_hidden(esk9_0,esk5_0)
      | ~ r2_hidden(k1_funct_1(esk8_0,esk9_0),esk7_0) )
    & ( r2_hidden(esk9_0,esk5_0)
      | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk6_0,esk8_0,esk7_0)) )
    & ( r2_hidden(k1_funct_1(esk8_0,esk9_0),esk7_0)
      | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk6_0,esk8_0,esk7_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_13,plain,(
    ! [X33,X34,X35,X36] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k8_relset_1(X33,X34,X35,X36) = k10_relat_1(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_14,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_relat_1(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_15,plain,(
    ! [X20,X21] : v1_relat_1(k2_zfmisc_1(X20,X21)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_16,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | k1_relset_1(X30,X31,X32) = k1_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_17,plain,(
    ! [X40,X41,X42] :
      ( ( ~ v1_funct_2(X42,X40,X41)
        | X40 = k1_relset_1(X40,X41,X42)
        | X41 = k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( X40 != k1_relset_1(X40,X41,X42)
        | v1_funct_2(X42,X40,X41)
        | X41 = k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( ~ v1_funct_2(X42,X40,X41)
        | X40 = k1_relset_1(X40,X41,X42)
        | X40 != k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( X40 != k1_relset_1(X40,X41,X42)
        | v1_funct_2(X42,X40,X41)
        | X40 != k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( ~ v1_funct_2(X42,X40,X41)
        | X42 = k1_xboole_0
        | X40 = k1_xboole_0
        | X41 != k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( X42 != k1_xboole_0
        | v1_funct_2(X42,X40,X41)
        | X40 = k1_xboole_0
        | X41 != k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk9_0,esk5_0)
    | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk6_0,esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk9_0,k10_relat_1(esk8_0,esk7_0))
    | r2_hidden(esk9_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_22]),c_0_24])])).

cnf(c_0_31,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk9_0,k1_relat_1(esk8_0))
    | r2_hidden(esk9_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_35,negated_conjecture,
    ( esk5_0 = k1_relat_1(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_22])]),c_0_33])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk9_0,k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_38,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_39,plain,(
    ! [X8,X9,X10,X11,X13,X14,X15,X16,X18] :
      ( ( r2_hidden(k4_tarski(X11,esk1_4(X8,X9,X10,X11)),X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k10_relat_1(X8,X9)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(esk1_4(X8,X9,X10,X11),X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k10_relat_1(X8,X9)
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(k4_tarski(X13,X14),X8)
        | ~ r2_hidden(X14,X9)
        | r2_hidden(X13,X10)
        | X10 != k10_relat_1(X8,X9)
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(esk2_3(X8,X15,X16),X16)
        | ~ r2_hidden(k4_tarski(esk2_3(X8,X15,X16),X18),X8)
        | ~ r2_hidden(X18,X15)
        | X16 = k10_relat_1(X8,X15)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(k4_tarski(esk2_3(X8,X15,X16),esk3_3(X8,X15,X16)),X8)
        | r2_hidden(esk2_3(X8,X15,X16),X16)
        | X16 = k10_relat_1(X8,X15)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(esk3_3(X8,X15,X16),X15)
        | r2_hidden(esk2_3(X8,X15,X16),X16)
        | X16 = k10_relat_1(X8,X15)
        | ~ v1_relat_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,X1),esk8_0)
    | X1 != k1_funct_1(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_29]),c_0_30])])).

cnf(c_0_41,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,plain,
    ( esk4_3(X1,X2,X3) = k1_funct_1(X3,X1)
    | ~ v1_funct_1(X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_19])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk8_0,esk9_0),esk7_0)
    | r2_hidden(esk9_0,k8_relset_1(esk5_0,esk6_0,esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k8_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))
    | ~ r2_hidden(esk9_0,esk5_0)
    | ~ r2_hidden(k1_funct_1(esk8_0,esk9_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,k1_funct_1(esk8_0,esk9_0)),esk8_0) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk8_0,esk9_0),esk7_0)
    | r2_hidden(esk9_0,k10_relat_1(esk8_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_21]),c_0_22])])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k10_relat_1(esk8_0,esk7_0))
    | ~ r2_hidden(k1_funct_1(esk8_0,esk9_0),esk7_0)
    | ~ r2_hidden(esk9_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_21]),c_0_22])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk9_0,X1)
    | X1 != k10_relat_1(esk8_0,X2)
    | ~ r2_hidden(k1_funct_1(esk8_0,esk9_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_30])])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk8_0,esk9_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_29]),c_0_30])])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k10_relat_1(esk8_0,esk7_0))
    | ~ r2_hidden(k1_funct_1(esk8_0,esk9_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_35]),c_0_37])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk9_0,X1)
    | X1 != k10_relat_1(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k10_relat_1(esk8_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_51])])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_53]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t46_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(X2!=k1_xboole_0=>![X5]:(r2_hidden(X5,k8_relset_1(X1,X2,X4,X3))<=>(r2_hidden(X5,X1)&r2_hidden(k1_funct_1(X4,X5),X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_funct_2)).
% 0.13/0.38  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.13/0.38  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.13/0.38  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.13/0.38  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.13/0.38  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.13/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.38  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.13/0.38  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 0.13/0.38  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(X2!=k1_xboole_0=>![X5]:(r2_hidden(X5,k8_relset_1(X1,X2,X4,X3))<=>(r2_hidden(X5,X1)&r2_hidden(k1_funct_1(X4,X5),X3)))))), inference(assume_negation,[status(cth)],[t46_funct_2])).
% 0.13/0.38  fof(c_0_10, plain, ![X27, X28, X29]:(((r2_hidden(X27,k1_relat_1(X29))|~r2_hidden(k4_tarski(X27,X28),X29)|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(X28=k1_funct_1(X29,X27)|~r2_hidden(k4_tarski(X27,X28),X29)|(~v1_relat_1(X29)|~v1_funct_1(X29))))&(~r2_hidden(X27,k1_relat_1(X29))|X28!=k1_funct_1(X29,X27)|r2_hidden(k4_tarski(X27,X28),X29)|(~v1_relat_1(X29)|~v1_funct_1(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.13/0.38  fof(c_0_11, plain, ![X22, X23, X24, X26]:((((r2_hidden(esk4_3(X22,X23,X24),k2_relat_1(X24))|~r2_hidden(X22,k10_relat_1(X24,X23))|~v1_relat_1(X24))&(r2_hidden(k4_tarski(X22,esk4_3(X22,X23,X24)),X24)|~r2_hidden(X22,k10_relat_1(X24,X23))|~v1_relat_1(X24)))&(r2_hidden(esk4_3(X22,X23,X24),X23)|~r2_hidden(X22,k10_relat_1(X24,X23))|~v1_relat_1(X24)))&(~r2_hidden(X26,k2_relat_1(X24))|~r2_hidden(k4_tarski(X22,X26),X24)|~r2_hidden(X26,X23)|r2_hidden(X22,k10_relat_1(X24,X23))|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.13/0.38  fof(c_0_12, negated_conjecture, (((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk5_0,esk6_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(esk6_0!=k1_xboole_0&((~r2_hidden(esk9_0,k8_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))|(~r2_hidden(esk9_0,esk5_0)|~r2_hidden(k1_funct_1(esk8_0,esk9_0),esk7_0)))&((r2_hidden(esk9_0,esk5_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk6_0,esk8_0,esk7_0)))&(r2_hidden(k1_funct_1(esk8_0,esk9_0),esk7_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.13/0.38  fof(c_0_13, plain, ![X33, X34, X35, X36]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k8_relset_1(X33,X34,X35,X36)=k10_relat_1(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.13/0.38  fof(c_0_14, plain, ![X6, X7]:(~v1_relat_1(X6)|(~m1_subset_1(X7,k1_zfmisc_1(X6))|v1_relat_1(X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.13/0.38  fof(c_0_15, plain, ![X20, X21]:v1_relat_1(k2_zfmisc_1(X20,X21)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.13/0.38  fof(c_0_16, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|k1_relset_1(X30,X31,X32)=k1_relat_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.38  fof(c_0_17, plain, ![X40, X41, X42]:((((~v1_funct_2(X42,X40,X41)|X40=k1_relset_1(X40,X41,X42)|X41=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(X40!=k1_relset_1(X40,X41,X42)|v1_funct_2(X42,X40,X41)|X41=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))))&((~v1_funct_2(X42,X40,X41)|X40=k1_relset_1(X40,X41,X42)|X40!=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(X40!=k1_relset_1(X40,X41,X42)|v1_funct_2(X42,X40,X41)|X40!=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))))&((~v1_funct_2(X42,X40,X41)|X42=k1_xboole_0|X40=k1_xboole_0|X41!=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(X42!=k1_xboole_0|v1_funct_2(X42,X40,X41)|X40=k1_xboole_0|X41!=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.13/0.38  cnf(c_0_18, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_19, plain, (r2_hidden(k4_tarski(X1,esk4_3(X1,X2,X3)),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (r2_hidden(esk9_0,esk5_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_21, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_23, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_24, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_25, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_26, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_27, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_funct_1(X2)|~r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(esk9_0,k10_relat_1(esk8_0,esk7_0))|r2_hidden(esk9_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_22]), c_0_24])])).
% 0.13/0.38  cnf(c_0_31, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (r2_hidden(esk9_0,k1_relat_1(esk8_0))|r2_hidden(esk9_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (esk5_0=k1_relat_1(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_22])]), c_0_33])).
% 0.13/0.38  cnf(c_0_36, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (r2_hidden(esk9_0,k1_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])])).
% 0.13/0.38  cnf(c_0_38, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  fof(c_0_39, plain, ![X8, X9, X10, X11, X13, X14, X15, X16, X18]:((((r2_hidden(k4_tarski(X11,esk1_4(X8,X9,X10,X11)),X8)|~r2_hidden(X11,X10)|X10!=k10_relat_1(X8,X9)|~v1_relat_1(X8))&(r2_hidden(esk1_4(X8,X9,X10,X11),X9)|~r2_hidden(X11,X10)|X10!=k10_relat_1(X8,X9)|~v1_relat_1(X8)))&(~r2_hidden(k4_tarski(X13,X14),X8)|~r2_hidden(X14,X9)|r2_hidden(X13,X10)|X10!=k10_relat_1(X8,X9)|~v1_relat_1(X8)))&((~r2_hidden(esk2_3(X8,X15,X16),X16)|(~r2_hidden(k4_tarski(esk2_3(X8,X15,X16),X18),X8)|~r2_hidden(X18,X15))|X16=k10_relat_1(X8,X15)|~v1_relat_1(X8))&((r2_hidden(k4_tarski(esk2_3(X8,X15,X16),esk3_3(X8,X15,X16)),X8)|r2_hidden(esk2_3(X8,X15,X16),X16)|X16=k10_relat_1(X8,X15)|~v1_relat_1(X8))&(r2_hidden(esk3_3(X8,X15,X16),X15)|r2_hidden(esk2_3(X8,X15,X16),X16)|X16=k10_relat_1(X8,X15)|~v1_relat_1(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,X1),esk8_0)|X1!=k1_funct_1(esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_29]), c_0_30])])).
% 0.13/0.38  cnf(c_0_41, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_42, plain, (esk4_3(X1,X2,X3)=k1_funct_1(X3,X1)|~v1_funct_1(X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_38, c_0_19])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (r2_hidden(k1_funct_1(esk8_0,esk9_0),esk7_0)|r2_hidden(esk9_0,k8_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (~r2_hidden(esk9_0,k8_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))|~r2_hidden(esk9_0,esk5_0)|~r2_hidden(k1_funct_1(esk8_0,esk9_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_45, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,k1_funct_1(esk8_0,esk9_0)),esk8_0)), inference(er,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_47, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~v1_funct_1(X1)|~r2_hidden(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (r2_hidden(k1_funct_1(esk8_0,esk9_0),esk7_0)|r2_hidden(esk9_0,k10_relat_1(esk8_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_21]), c_0_22])])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (~r2_hidden(esk9_0,k10_relat_1(esk8_0,esk7_0))|~r2_hidden(k1_funct_1(esk8_0,esk9_0),esk7_0)|~r2_hidden(esk9_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_21]), c_0_22])])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (r2_hidden(esk9_0,X1)|X1!=k10_relat_1(esk8_0,X2)|~r2_hidden(k1_funct_1(esk8_0,esk9_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_30])])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (r2_hidden(k1_funct_1(esk8_0,esk9_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_29]), c_0_30])])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (~r2_hidden(esk9_0,k10_relat_1(esk8_0,esk7_0))|~r2_hidden(k1_funct_1(esk8_0,esk9_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_35]), c_0_37])])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (r2_hidden(esk9_0,X1)|X1!=k10_relat_1(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (~r2_hidden(esk9_0,k10_relat_1(esk8_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_51])])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_53]), c_0_54]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 56
% 0.13/0.38  # Proof object clause steps            : 37
% 0.13/0.38  # Proof object formula steps           : 19
% 0.13/0.38  # Proof object conjectures             : 25
% 0.13/0.38  # Proof object clause conjectures      : 22
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 18
% 0.13/0.38  # Proof object initial formulas used   : 9
% 0.13/0.38  # Proof object generating inferences   : 16
% 0.13/0.38  # Proof object simplifying inferences  : 30
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 10
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 32
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 32
% 0.13/0.38  # Processed clauses                    : 172
% 0.13/0.38  # ...of these trivial                  : 6
% 0.13/0.38  # ...subsumed                          : 39
% 0.13/0.38  # ...remaining for further processing  : 127
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 26
% 0.13/0.38  # Generated clauses                    : 237
% 0.13/0.38  # ...of the previous two non-trivial   : 189
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 229
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 8
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 69
% 0.13/0.38  #    Positive orientable unit clauses  : 10
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 57
% 0.13/0.38  # Current number of unprocessed clauses: 81
% 0.13/0.38  # ...number of literals in the above   : 425
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 58
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1136
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 418
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 35
% 0.13/0.38  # Unit Clause-clause subsumption calls : 21
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 12
% 0.13/0.38  # BW rewrite match successes           : 5
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 7717
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.039 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.044 s
% 0.13/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
