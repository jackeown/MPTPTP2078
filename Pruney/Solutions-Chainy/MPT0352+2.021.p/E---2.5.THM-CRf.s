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
% DateTime   : Thu Dec  3 10:45:39 EST 2020

% Result     : Theorem 0.84s
% Output     : CNFRefutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 998 expanded)
%              Number of clauses        :   56 ( 427 expanded)
%              Number of leaves         :   14 ( 249 expanded)
%              Depth                    :   14
%              Number of atoms          :  129 (2140 expanded)
%              Number of equality atoms :   56 ( 584 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t29_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t35_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k4_xboole_0(X1,X4),k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(X2,X3)
            <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_subset_1])).

fof(c_0_15,plain,(
    ! [X50,X51] :
      ( ~ m1_subset_1(X51,k1_zfmisc_1(X50))
      | k3_subset_1(X50,X51) = k4_xboole_0(X50,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    & ( ~ r1_tarski(esk2_0,esk3_0)
      | ~ r1_tarski(k3_subset_1(esk1_0,esk3_0),k3_subset_1(esk1_0,esk2_0)) )
    & ( r1_tarski(esk2_0,esk3_0)
      | r1_tarski(k3_subset_1(esk1_0,esk3_0),k3_subset_1(esk1_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_17,plain,(
    ! [X54,X55] :
      ( ~ m1_subset_1(X55,k1_zfmisc_1(X54))
      | k3_subset_1(X54,k3_subset_1(X54,X55)) = X55 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_18,plain,(
    ! [X52,X53] :
      ( ~ m1_subset_1(X53,k1_zfmisc_1(X52))
      | m1_subset_1(k3_subset_1(X52,X53),k1_zfmisc_1(X52)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_19,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X14,X15,X16] : r1_tarski(k3_xboole_0(X14,X15),k2_xboole_0(X14,X16)) ),
    inference(variable_rename,[status(thm)],[t29_xboole_1])).

fof(c_0_23,plain,(
    ! [X34,X35] : k4_xboole_0(X34,k4_xboole_0(X34,X35)) = k3_xboole_0(X34,X35) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_24,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( k3_subset_1(esk1_0,esk3_0) = k4_xboole_0(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_27,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(esk1_0,esk3_0),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_20])])).

cnf(c_0_30,negated_conjecture,
    ( k3_subset_1(esk1_0,k4_xboole_0(esk1_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_32,plain,(
    ! [X40,X41] : k2_xboole_0(k3_xboole_0(X40,X41),k4_xboole_0(X40,X41)) = X40 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_29]),c_0_30])).

fof(c_0_35,plain,(
    ! [X13] : k2_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_36,negated_conjecture,
    ( k3_subset_1(esk1_0,esk2_0) = k4_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_31])).

fof(c_0_38,plain,(
    ! [X27,X28] : k4_xboole_0(k2_xboole_0(X27,X28),X28) = k4_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_39,plain,(
    ! [X25,X26] : k2_xboole_0(X25,k4_xboole_0(X26,X25)) = k2_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_40,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_41,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_42,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_36]),c_0_31])])).

cnf(c_0_46,negated_conjecture,
    ( k3_subset_1(esk1_0,k4_xboole_0(esk1_0,esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_47,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_40,c_0_28])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_45]),c_0_46])).

fof(c_0_54,plain,(
    ! [X19,X20,X21,X22] :
      ( ~ r1_tarski(X19,X20)
      | ~ r1_tarski(X21,X22)
      | r1_tarski(k4_xboole_0(X19,X22),k4_xboole_0(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_xboole_1])])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0)
    | r1_tarski(k3_subset_1(esk1_0,esk3_0),k3_subset_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_56,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_57,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_48]),c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_53])).

cnf(c_0_60,plain,
    ( r1_tarski(k4_xboole_0(X1,X4),k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk1_0,esk2_0))
    | r1_tarski(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_25]),c_0_36])).

cnf(c_0_62,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),esk2_0) = k4_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_53]),c_0_50]),c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_53])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,X2) = k4_xboole_0(esk3_0,esk1_0)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_51,c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_57])).

fof(c_0_67,plain,(
    ! [X39] : k4_xboole_0(k1_xboole_0,X39) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk3_0)
    | ~ r1_tarski(k3_subset_1(esk1_0,esk3_0),k3_subset_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(esk1_0,esk2_0)),k4_xboole_0(X2,k4_xboole_0(esk1_0,esk3_0)))
    | r1_tarski(esk2_0,esk3_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_62]),c_0_48]),c_0_50]),c_0_63]),c_0_53])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k4_xboole_0(esk3_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_64,c_0_58])).

cnf(c_0_72,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk1_0) = k4_xboole_0(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_44,c_0_50])).

cnf(c_0_74,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk1_0,esk2_0))
    | ~ r1_tarski(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_25]),c_0_36])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_66]),c_0_70]),c_0_34])])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k4_xboole_0(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,plain,
    ( k4_xboole_0(X1,X2) = k4_xboole_0(esk2_0,esk1_0)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_65,c_0_72])).

cnf(c_0_79,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_73]),c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76])])).

cnf(c_0_81,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X3,X4))
    | k4_xboole_0(X4,X2) != k4_xboole_0(esk2_0,esk1_0)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_60,c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = k4_xboole_0(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_76])).

cnf(c_0_83,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_83])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:34:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.84/1.00  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.84/1.00  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.84/1.00  #
% 0.84/1.00  # Preprocessing time       : 0.028 s
% 0.84/1.00  # Presaturation interreduction done
% 0.84/1.00  
% 0.84/1.00  # Proof found!
% 0.84/1.00  # SZS status Theorem
% 0.84/1.00  # SZS output start CNFRefutation
% 0.84/1.00  fof(t31_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 0.84/1.00  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.84/1.00  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.84/1.00  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.84/1.00  fof(t29_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_xboole_1)).
% 0.84/1.00  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.84/1.00  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.84/1.00  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.84/1.00  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.84/1.00  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.84/1.00  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.84/1.00  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.84/1.00  fof(t35_xboole_1, axiom, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k4_xboole_0(X1,X4),k4_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_xboole_1)).
% 0.84/1.00  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.84/1.00  fof(c_0_14, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t31_subset_1])).
% 0.84/1.00  fof(c_0_15, plain, ![X50, X51]:(~m1_subset_1(X51,k1_zfmisc_1(X50))|k3_subset_1(X50,X51)=k4_xboole_0(X50,X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.84/1.00  fof(c_0_16, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))&((~r1_tarski(esk2_0,esk3_0)|~r1_tarski(k3_subset_1(esk1_0,esk3_0),k3_subset_1(esk1_0,esk2_0)))&(r1_tarski(esk2_0,esk3_0)|r1_tarski(k3_subset_1(esk1_0,esk3_0),k3_subset_1(esk1_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.84/1.00  fof(c_0_17, plain, ![X54, X55]:(~m1_subset_1(X55,k1_zfmisc_1(X54))|k3_subset_1(X54,k3_subset_1(X54,X55))=X55), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.84/1.00  fof(c_0_18, plain, ![X52, X53]:(~m1_subset_1(X53,k1_zfmisc_1(X52))|m1_subset_1(k3_subset_1(X52,X53),k1_zfmisc_1(X52))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.84/1.00  cnf(c_0_19, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.84/1.00  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.84/1.00  cnf(c_0_21, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.84/1.00  fof(c_0_22, plain, ![X14, X15, X16]:r1_tarski(k3_xboole_0(X14,X15),k2_xboole_0(X14,X16)), inference(variable_rename,[status(thm)],[t29_xboole_1])).
% 0.84/1.00  fof(c_0_23, plain, ![X34, X35]:k4_xboole_0(X34,k4_xboole_0(X34,X35))=k3_xboole_0(X34,X35), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.84/1.00  cnf(c_0_24, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.84/1.00  cnf(c_0_25, negated_conjecture, (k3_subset_1(esk1_0,esk3_0)=k4_xboole_0(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.84/1.00  cnf(c_0_26, negated_conjecture, (k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_21, c_0_20])).
% 0.84/1.00  cnf(c_0_27, plain, (r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.84/1.00  cnf(c_0_28, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.84/1.00  cnf(c_0_29, negated_conjecture, (m1_subset_1(k4_xboole_0(esk1_0,esk3_0),k1_zfmisc_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_20])])).
% 0.84/1.00  cnf(c_0_30, negated_conjecture, (k3_subset_1(esk1_0,k4_xboole_0(esk1_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[c_0_26, c_0_25])).
% 0.84/1.00  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.84/1.00  fof(c_0_32, plain, ![X40, X41]:k2_xboole_0(k3_xboole_0(X40,X41),k4_xboole_0(X40,X41))=X40, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.84/1.00  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.84/1.00  cnf(c_0_34, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_29]), c_0_30])).
% 0.84/1.00  fof(c_0_35, plain, ![X13]:k2_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.84/1.00  cnf(c_0_36, negated_conjecture, (k3_subset_1(esk1_0,esk2_0)=k4_xboole_0(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_19, c_0_31])).
% 0.84/1.00  cnf(c_0_37, negated_conjecture, (k3_subset_1(esk1_0,k3_subset_1(esk1_0,esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_21, c_0_31])).
% 0.84/1.00  fof(c_0_38, plain, ![X27, X28]:k4_xboole_0(k2_xboole_0(X27,X28),X28)=k4_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.84/1.00  fof(c_0_39, plain, ![X25, X26]:k2_xboole_0(X25,k4_xboole_0(X26,X25))=k2_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.84/1.00  cnf(c_0_40, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.84/1.00  fof(c_0_41, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.84/1.00  fof(c_0_42, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.84/1.00  cnf(c_0_43, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(esk1_0,X1))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.84/1.00  cnf(c_0_44, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.84/1.00  cnf(c_0_45, negated_conjecture, (m1_subset_1(k4_xboole_0(esk1_0,esk2_0),k1_zfmisc_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_36]), c_0_31])])).
% 0.84/1.00  cnf(c_0_46, negated_conjecture, (k3_subset_1(esk1_0,k4_xboole_0(esk1_0,esk2_0))=esk2_0), inference(rw,[status(thm)],[c_0_37, c_0_36])).
% 0.84/1.00  cnf(c_0_47, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.84/1.00  cnf(c_0_48, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.84/1.00  cnf(c_0_49, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_40, c_0_28])).
% 0.84/1.00  cnf(c_0_50, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.84/1.00  cnf(c_0_51, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.84/1.00  cnf(c_0_52, negated_conjecture, (r1_tarski(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.84/1.00  cnf(c_0_53, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_45]), c_0_46])).
% 0.84/1.00  fof(c_0_54, plain, ![X19, X20, X21, X22]:(~r1_tarski(X19,X20)|~r1_tarski(X21,X22)|r1_tarski(k4_xboole_0(X19,X22),k4_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_xboole_1])])).
% 0.84/1.00  cnf(c_0_55, negated_conjecture, (r1_tarski(esk2_0,esk3_0)|r1_tarski(k3_subset_1(esk1_0,esk3_0),k3_subset_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.84/1.00  cnf(c_0_56, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.84/1.00  cnf(c_0_57, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_48]), c_0_50])).
% 0.84/1.00  cnf(c_0_58, negated_conjecture, (k1_xboole_0=k4_xboole_0(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.84/1.00  cnf(c_0_59, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(esk1_0,X1))), inference(spm,[status(thm)],[c_0_33, c_0_53])).
% 0.84/1.00  cnf(c_0_60, plain, (r1_tarski(k4_xboole_0(X1,X4),k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.84/1.00  cnf(c_0_61, negated_conjecture, (r1_tarski(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk1_0,esk2_0))|r1_tarski(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_25]), c_0_36])).
% 0.84/1.00  cnf(c_0_62, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk1_0,esk2_0),esk2_0)=k4_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_53]), c_0_50]), c_0_57])).
% 0.84/1.00  cnf(c_0_63, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)=esk1_0), inference(spm,[status(thm)],[c_0_57, c_0_53])).
% 0.84/1.00  cnf(c_0_64, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.84/1.00  cnf(c_0_65, plain, (k4_xboole_0(X1,X2)=k4_xboole_0(esk3_0,esk1_0)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_51, c_0_58])).
% 0.84/1.00  cnf(c_0_66, negated_conjecture, (r1_tarski(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_59, c_0_57])).
% 0.84/1.00  fof(c_0_67, plain, ![X39]:k4_xboole_0(k1_xboole_0,X39)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.84/1.00  cnf(c_0_68, negated_conjecture, (~r1_tarski(esk2_0,esk3_0)|~r1_tarski(k3_subset_1(esk1_0,esk3_0),k3_subset_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.84/1.00  cnf(c_0_69, negated_conjecture, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(esk1_0,esk2_0)),k4_xboole_0(X2,k4_xboole_0(esk1_0,esk3_0)))|r1_tarski(esk2_0,esk3_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.84/1.00  cnf(c_0_70, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk2_0))=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_62]), c_0_48]), c_0_50]), c_0_63]), c_0_53])).
% 0.84/1.00  cnf(c_0_71, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k4_xboole_0(esk3_0,esk1_0)), inference(rw,[status(thm)],[c_0_64, c_0_58])).
% 0.84/1.00  cnf(c_0_72, negated_conjecture, (k4_xboole_0(esk3_0,esk1_0)=k4_xboole_0(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.84/1.00  cnf(c_0_73, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_44, c_0_50])).
% 0.84/1.00  cnf(c_0_74, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.84/1.00  cnf(c_0_75, negated_conjecture, (~r1_tarski(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk1_0,esk2_0))|~r1_tarski(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_25]), c_0_36])).
% 0.84/1.00  cnf(c_0_76, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_66]), c_0_70]), c_0_34])])).
% 0.84/1.00  cnf(c_0_77, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k4_xboole_0(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_71, c_0_72])).
% 0.84/1.00  cnf(c_0_78, plain, (k4_xboole_0(X1,X2)=k4_xboole_0(esk2_0,esk1_0)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_65, c_0_72])).
% 0.84/1.00  cnf(c_0_79, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_73]), c_0_74])).
% 0.84/1.00  cnf(c_0_80, negated_conjecture, (~r1_tarski(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76])])).
% 0.84/1.00  cnf(c_0_81, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X3,X4))|k4_xboole_0(X4,X2)!=k4_xboole_0(esk2_0,esk1_0)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_60, c_0_77])).
% 0.84/1.00  cnf(c_0_82, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=k4_xboole_0(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_78, c_0_76])).
% 0.84/1.00  cnf(c_0_83, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_64, c_0_79])).
% 0.84/1.00  cnf(c_0_84, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82]), c_0_83])]), ['proof']).
% 0.84/1.00  # SZS output end CNFRefutation
% 0.84/1.00  # Proof object total steps             : 85
% 0.84/1.00  # Proof object clause steps            : 56
% 0.84/1.00  # Proof object formula steps           : 29
% 0.84/1.00  # Proof object conjectures             : 33
% 0.84/1.00  # Proof object clause conjectures      : 30
% 0.84/1.00  # Proof object formula conjectures     : 3
% 0.84/1.00  # Proof object initial clauses used    : 18
% 0.84/1.00  # Proof object initial formulas used   : 14
% 0.84/1.00  # Proof object generating inferences   : 26
% 0.84/1.00  # Proof object simplifying inferences  : 36
% 0.84/1.00  # Training examples: 0 positive, 0 negative
% 0.84/1.00  # Parsed axioms                        : 25
% 0.84/1.00  # Removed by relevancy pruning/SinE    : 0
% 0.84/1.00  # Initial clauses                      : 30
% 0.84/1.00  # Removed in clause preprocessing      : 1
% 0.84/1.00  # Initial clauses in saturation        : 29
% 0.84/1.00  # Processed clauses                    : 2415
% 0.84/1.00  # ...of these trivial                  : 105
% 0.84/1.00  # ...subsumed                          : 1820
% 0.84/1.00  # ...remaining for further processing  : 490
% 0.84/1.00  # Other redundant clauses eliminated   : 6
% 0.84/1.00  # Clauses deleted for lack of memory   : 0
% 0.84/1.00  # Backward-subsumed                    : 7
% 0.84/1.00  # Backward-rewritten                   : 83
% 0.84/1.00  # Generated clauses                    : 49131
% 0.84/1.00  # ...of the previous two non-trivial   : 42457
% 0.84/1.00  # Contextual simplify-reflections      : 0
% 0.84/1.00  # Paramodulations                      : 49125
% 0.84/1.00  # Factorizations                       : 0
% 0.84/1.00  # Equation resolutions                 : 6
% 0.84/1.00  # Propositional unsat checks           : 0
% 0.84/1.00  #    Propositional check models        : 0
% 0.84/1.00  #    Propositional check unsatisfiable : 0
% 0.84/1.00  #    Propositional clauses             : 0
% 0.84/1.00  #    Propositional clauses after purity: 0
% 0.84/1.00  #    Propositional unsat core size     : 0
% 0.84/1.00  #    Propositional preprocessing time  : 0.000
% 0.84/1.00  #    Propositional encoding time       : 0.000
% 0.84/1.00  #    Propositional solver time         : 0.000
% 0.84/1.00  #    Success case prop preproc time    : 0.000
% 0.84/1.00  #    Success case prop encoding time   : 0.000
% 0.84/1.00  #    Success case prop solver time     : 0.000
% 0.84/1.00  # Current number of processed clauses  : 373
% 0.84/1.00  #    Positive orientable unit clauses  : 128
% 0.84/1.00  #    Positive unorientable unit clauses: 32
% 0.84/1.00  #    Negative unit clauses             : 20
% 0.84/1.00  #    Non-unit-clauses                  : 193
% 0.84/1.00  # Current number of unprocessed clauses: 39758
% 0.84/1.00  # ...number of literals in the above   : 46344
% 0.84/1.00  # Current number of archived formulas  : 0
% 0.84/1.00  # Current number of archived clauses   : 118
% 0.84/1.00  # Clause-clause subsumption calls (NU) : 5817
% 0.84/1.00  # Rec. Clause-clause subsumption calls : 5769
% 0.84/1.00  # Non-unit clause-clause subsumptions  : 644
% 0.84/1.00  # Unit Clause-clause subsumption calls : 1314
% 0.84/1.00  # Rewrite failures with RHS unbound    : 40
% 0.84/1.00  # BW rewrite match attempts            : 3299
% 0.84/1.00  # BW rewrite match successes           : 190
% 0.84/1.00  # Condensation attempts                : 0
% 0.84/1.00  # Condensation successes               : 0
% 0.84/1.00  # Termbank termtop insertions          : 1166485
% 0.84/1.00  
% 0.84/1.00  # -------------------------------------------------
% 0.84/1.00  # User time                : 0.632 s
% 0.84/1.00  # System time              : 0.031 s
% 0.84/1.00  # Total time               : 0.663 s
% 0.84/1.00  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
