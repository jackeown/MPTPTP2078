%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0822+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:14 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 762 expanded)
%              Number of clauses        :   36 ( 354 expanded)
%              Number of leaves         :    7 ( 175 expanded)
%              Depth                    :   15
%              Number of atoms          :  141 (2674 expanded)
%              Number of equality atoms :   38 ( 759 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_relset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] : ~ r2_hidden(k4_tarski(X5,X4),X3) )
      <=> k2_relset_1(X1,X2,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ( ! [X4] :
              ~ ( r2_hidden(X4,X2)
                & ! [X5] : ~ r2_hidden(k4_tarski(X5,X4),X3) )
        <=> k2_relset_1(X1,X2,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t23_relset_1])).

fof(c_0_8,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | k2_relset_1(X20,X21,X22) = k2_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_9,negated_conjecture,(
    ! [X35,X36] :
      ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
      & ( r2_hidden(esk7_0,esk5_0)
        | k2_relset_1(esk4_0,esk5_0,esk6_0) != esk5_0 )
      & ( ~ r2_hidden(k4_tarski(X35,esk7_0),esk6_0)
        | k2_relset_1(esk4_0,esk5_0,esk6_0) != esk5_0 )
      & ( ~ r2_hidden(X36,esk5_0)
        | r2_hidden(k4_tarski(esk8_1(X36),X36),esk6_0)
        | k2_relset_1(esk4_0,esk5_0,esk6_0) = esk5_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])])).

fof(c_0_10,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | m1_subset_1(k2_relset_1(X17,X18,X19),k1_zfmisc_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_11,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X6,X7,X8,X10,X11,X12,X13,X15] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),X8),X6)
        | X7 != k2_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(X11,X10),X6)
        | r2_hidden(X10,X7)
        | X7 != k2_relat_1(X6) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | ~ r2_hidden(k4_tarski(X15,esk2_2(X12,X13)),X12)
        | X13 = k2_relat_1(X12) )
      & ( r2_hidden(esk2_2(X12,X13),X13)
        | r2_hidden(k4_tarski(esk3_2(X12,X13),esk2_2(X12,X13)),X12)
        | X13 = k2_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_14,plain,(
    ! [X25,X26,X27] :
      ( ~ r2_hidden(X25,X26)
      | ~ m1_subset_1(X26,k1_zfmisc_1(X27))
      | m1_subset_1(X25,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_15,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( k2_relset_1(esk4_0,esk5_0,esk6_0) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk6_0),k1_zfmisc_1(esk5_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_12]),c_0_16])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk3_2(X1,X2),esk2_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X23,X24)
      | v1_xboole_0(X24)
      | r2_hidden(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( X1 = k2_relat_1(X2)
    | r2_hidden(esk2_2(X2,X1),k2_relat_1(X2))
    | r2_hidden(esk2_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_1(X1),X1),esk6_0)
    | k2_relset_1(esk4_0,esk5_0,esk6_0) = esk5_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( X1 = k2_relat_1(esk6_0)
    | m1_subset_1(esk2_2(esk6_0,X1),esk5_0)
    | r2_hidden(esk2_2(esk6_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_28,plain,(
    ! [X28,X29,X30] :
      ( ~ r2_hidden(X28,X29)
      | ~ m1_subset_1(X29,k1_zfmisc_1(X30))
      | ~ v1_xboole_0(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_29,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(X3,esk2_2(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk5_0
    | r2_hidden(k4_tarski(esk8_1(X1),X1),esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( X1 = k2_relat_1(esk6_0)
    | v1_xboole_0(esk5_0)
    | r2_hidden(esk2_2(esk6_0,X1),esk5_0)
    | r2_hidden(esk2_2(esk6_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk5_0
    | X1 = k2_relat_1(esk6_0)
    | ~ r2_hidden(esk2_2(esk6_0,X1),esk5_0)
    | ~ r2_hidden(esk2_2(esk6_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk5_0
    | v1_xboole_0(esk5_0)
    | r2_hidden(esk2_2(esk6_0,esk5_0),esk5_0) ),
    inference(ef,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0)
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_19])).

cnf(c_0_36,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk5_0
    | v1_xboole_0(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk7_0),esk6_0)
    | k2_relset_1(esk4_0,esk5_0,esk6_0) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk5_0
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk5_0
    | r2_hidden(X1,k2_relat_1(esk6_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( k2_relat_1(esk6_0) != esk5_0
    | ~ r2_hidden(k4_tarski(X1,esk7_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_16])).

cnf(c_0_42,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk5_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk5_0
    | X1 = k2_relat_1(esk6_0)
    | r2_hidden(esk2_2(esk6_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk7_0,esk5_0)
    | k2_relset_1(esk4_0,esk5_0,esk6_0) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_46,negated_conjecture,
    ( k2_relat_1(esk6_0) != esk5_0
    | ~ r2_hidden(esk7_0,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk7_0,esk5_0)
    | k2_relat_1(esk6_0) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_45,c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(esk7_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_47])])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_47])]),c_0_49]),
    [proof]).

%------------------------------------------------------------------------------
