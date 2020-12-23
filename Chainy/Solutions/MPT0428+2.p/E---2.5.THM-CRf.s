%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0428+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:45 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 108 expanded)
%              Number of clauses        :   28 (  46 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :  131 ( 280 expanded)
%              Number of equality atoms :   35 (  82 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t60_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( m1_setfam_1(X2,X1)
      <=> k5_setfam_1(X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',d4_subset_1)).

fof(d12_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_setfam_1(X2,X1)
    <=> r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT005+2.ax',fc1_subset_1)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',d1_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',d10_xboole_0)).

fof(t95_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t95_zfmisc_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t99_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( m1_setfam_1(X2,X1)
        <=> k5_setfam_1(X1,X2) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t60_setfam_1])).

fof(c_0_13,plain,(
    ! [X1575] : m1_subset_1(k2_subset_1(X1575),k1_zfmisc_1(X1575)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_14,plain,(
    ! [X1531] : k2_subset_1(X1531) = X1531 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_15,plain,(
    ! [X1840,X1841] :
      ( ( ~ m1_setfam_1(X1841,X1840)
        | r1_tarski(X1840,k3_tarski(X1841)) )
      & ( ~ r1_tarski(X1840,k3_tarski(X1841))
        | m1_setfam_1(X1841,X1840) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_setfam_1])])).

fof(c_0_16,negated_conjecture,
    ( m1_subset_1(esk112_0,k1_zfmisc_1(k1_zfmisc_1(esk111_0)))
    & ( ~ m1_setfam_1(esk112_0,esk111_0)
      | k5_setfam_1(esk111_0,esk112_0) != esk111_0 )
    & ( m1_setfam_1(esk112_0,esk111_0)
      | k5_setfam_1(esk111_0,esk112_0) = esk111_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_17,plain,(
    ! [X1496,X1497] :
      ( ( ~ m1_subset_1(X1497,X1496)
        | r2_hidden(X1497,X1496)
        | v1_xboole_0(X1496) )
      & ( ~ r2_hidden(X1497,X1496)
        | m1_subset_1(X1497,X1496)
        | v1_xboole_0(X1496) )
      & ( ~ m1_subset_1(X1497,X1496)
        | v1_xboole_0(X1497)
        | ~ v1_xboole_0(X1496) )
      & ( ~ v1_xboole_0(X1497)
        | m1_subset_1(X1497,X1496)
        | ~ v1_xboole_0(X1496) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_18,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X1600] : ~ v1_xboole_0(k1_zfmisc_1(X1600)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_21,plain,(
    ! [X1949,X1950] :
      ( ~ m1_subset_1(X1950,k1_zfmisc_1(k1_zfmisc_1(X1949)))
      | k5_setfam_1(X1949,X1950) = k3_tarski(X1950) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

cnf(c_0_22,plain,
    ( r1_tarski(X2,k3_tarski(X1))
    | ~ m1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( m1_setfam_1(esk112_0,esk111_0)
    | k5_setfam_1(esk111_0,esk112_0) = esk111_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( ~ m1_setfam_1(esk112_0,esk111_0)
    | k5_setfam_1(esk111_0,esk112_0) != esk111_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( m1_setfam_1(X2,X1)
    | ~ r1_tarski(X1,k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_26,plain,(
    ! [X982,X983,X984,X985,X986,X987] :
      ( ( ~ r2_hidden(X984,X983)
        | r1_tarski(X984,X982)
        | X983 != k1_zfmisc_1(X982) )
      & ( ~ r1_tarski(X985,X982)
        | r2_hidden(X985,X983)
        | X983 != k1_zfmisc_1(X982) )
      & ( ~ r2_hidden(esk21_2(X986,X987),X987)
        | ~ r1_tarski(esk21_2(X986,X987),X986)
        | X987 = k1_zfmisc_1(X986) )
      & ( r2_hidden(esk21_2(X986,X987),X987)
        | r1_tarski(esk21_2(X986,X987),X986)
        | X987 = k1_zfmisc_1(X986) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_30,plain,(
    ! [X104,X105] :
      ( ( r1_tarski(X104,X105)
        | X104 != X105 )
      & ( r1_tarski(X105,X104)
        | X104 != X105 )
      & ( ~ r1_tarski(X104,X105)
        | ~ r1_tarski(X105,X104)
        | X104 = X105 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_31,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( k5_setfam_1(esk111_0,esk112_0) = esk111_0
    | r1_tarski(esk111_0,k3_tarski(esk112_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk112_0,k1_zfmisc_1(k1_zfmisc_1(esk111_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_34,plain,(
    ! [X1450,X1451] :
      ( ~ r1_tarski(X1450,X1451)
      | r1_tarski(k3_tarski(X1450),k3_tarski(X1451)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

fof(c_0_35,plain,(
    ! [X1459] : k3_tarski(k1_zfmisc_1(X1459)) = X1459 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

fof(c_0_36,plain,(
    ! [X1998,X1999] :
      ( ( ~ m1_subset_1(X1998,k1_zfmisc_1(X1999))
        | r1_tarski(X1998,X1999) )
      & ( ~ r1_tarski(X1998,X1999)
        | m1_subset_1(X1998,k1_zfmisc_1(X1999)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_37,negated_conjecture,
    ( k5_setfam_1(esk111_0,esk112_0) != esk111_0
    | ~ r1_tarski(esk111_0,k3_tarski(esk112_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_40,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( k3_tarski(esk112_0) = esk111_0
    | r1_tarski(esk111_0,k3_tarski(esk112_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_42,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( k3_tarski(esk112_0) != esk111_0
    | ~ r1_tarski(esk111_0,k3_tarski(esk112_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_31]),c_0_33])])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k3_tarski(esk112_0) = esk111_0
    | ~ r1_tarski(k3_tarski(esk112_0),esk111_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk112_0,k1_zfmisc_1(esk111_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_33])).

cnf(c_0_50,negated_conjecture,
    ( k1_zfmisc_1(k3_tarski(esk112_0)) != k1_zfmisc_1(esk111_0)
    | k3_tarski(esk112_0) != esk111_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( k3_tarski(esk112_0) = esk111_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51]),c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
