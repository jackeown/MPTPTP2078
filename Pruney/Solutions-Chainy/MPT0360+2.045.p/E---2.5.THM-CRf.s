%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:15 EST 2020

% Result     : Theorem 0.83s
% Output     : CNFRefutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 268 expanded)
%              Number of clauses        :   44 ( 123 expanded)
%              Number of leaves         :   14 (  65 expanded)
%              Depth                    :   17
%              Number of atoms          :  160 ( 627 expanded)
%              Number of equality atoms :   36 ( 176 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t40_subset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X2,k3_subset_1(X1,X3)) )
       => X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(c_0_14,plain,(
    ! [X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(X31))
      | k3_subset_1(X31,X32) = k4_xboole_0(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_15,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X4,k3_xboole_0(X4,X5)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X1))
       => ( ( r1_tarski(X2,X3)
            & r1_tarski(X2,k3_subset_1(X1,X3)) )
         => X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t40_subset_1])).

cnf(c_0_17,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & r1_tarski(esk3_0,esk4_0)
    & r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0))
    & esk3_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_20,plain,(
    ! [X6,X7,X8] :
      ( ( r1_tarski(X6,X7)
        | ~ r1_tarski(X6,k4_xboole_0(X7,X8)) )
      & ( r1_xboole_0(X6,X8)
        | ~ r1_tarski(X6,k4_xboole_0(X7,X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_21,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,X17)
      | r1_xboole_0(X16,k4_xboole_0(X18,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

fof(c_0_24,plain,(
    ! [X14,X15] :
      ( ( ~ r1_xboole_0(X14,X15)
        | k4_xboole_0(X14,X15) = X14 )
      & ( k4_xboole_0(X14,X15) != X14
        | r1_xboole_0(X14,X15) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( k3_subset_1(esk2_0,esk4_0) = k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk3_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_32,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,X20)
      | ~ r1_xboole_0(X19,X21)
      | r1_tarski(X19,k4_xboole_0(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_18])).

cnf(c_0_36,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r1_xboole_0(esk3_0,k5_xboole_0(X1,k3_xboole_0(X1,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[c_0_37,c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_42,plain,(
    ! [X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X24,X23)
        | r1_tarski(X24,X22)
        | X23 != k1_zfmisc_1(X22) )
      & ( ~ r1_tarski(X25,X22)
        | r2_hidden(X25,X23)
        | X23 != k1_zfmisc_1(X22) )
      & ( ~ r2_hidden(esk1_2(X26,X27),X27)
        | ~ r1_tarski(esk1_2(X26,X27),X26)
        | X27 = k1_zfmisc_1(X26) )
      & ( r2_hidden(esk1_2(X26,X27),X27)
        | r1_tarski(esk1_2(X26,X27),X26)
        | X27 = k1_zfmisc_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk3_0,k5_xboole_0(X1,k3_xboole_0(X1,esk3_0)))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_34])).

fof(c_0_46,plain,(
    ! [X29,X30] :
      ( ( ~ m1_subset_1(X30,X29)
        | r2_hidden(X30,X29)
        | v1_xboole_0(X29) )
      & ( ~ r2_hidden(X30,X29)
        | m1_subset_1(X30,X29)
        | v1_xboole_0(X29) )
      & ( ~ m1_subset_1(X30,X29)
        | v1_xboole_0(X30)
        | ~ v1_xboole_0(X29) )
      & ( ~ v1_xboole_0(X30)
        | m1_subset_1(X30,X29)
        | ~ v1_xboole_0(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | X1 != k1_zfmisc_1(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0)))) ),
    inference(er,[status(thm)],[c_0_47])).

fof(c_0_50,plain,(
    ! [X10,X11] :
      ( v1_xboole_0(X11)
      | ~ r1_tarski(X11,X10)
      | ~ r1_xboole_0(X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

fof(c_0_51,plain,(
    ! [X12,X13] : r1_xboole_0(k4_xboole_0(X12,X13),X13) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_52,plain,(
    ! [X9] : k4_xboole_0(X9,k1_xboole_0) = X9 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_53,plain,
    ( m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0))))
    | v1_xboole_0(k1_zfmisc_1(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_57,plain,(
    ! [X35] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X35)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0))))
    | m1_subset_1(X1,k1_zfmisc_1(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0))))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( v1_xboole_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_36]),c_0_34])])).

cnf(c_0_61,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_56,c_0_18])).

fof(c_0_62,plain,(
    ! [X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X33))
      | k3_subset_1(X33,k3_subset_1(X33,X34)) = X34 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_63,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_58,c_0_18])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_61])).

cnf(c_0_67,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_63]),c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( k3_subset_1(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0)),esk3_0) = k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_65]),c_0_66])).

cnf(c_0_70,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_63]),c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_65]),c_0_69]),c_0_70]),c_0_71]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:29:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.83/1.01  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S064A
% 0.83/1.01  # and selection function SelectComplexG.
% 0.83/1.01  #
% 0.83/1.01  # Preprocessing time       : 0.027 s
% 0.83/1.01  # Presaturation interreduction done
% 0.83/1.01  
% 0.83/1.01  # Proof found!
% 0.83/1.01  # SZS status Theorem
% 0.83/1.01  # SZS output start CNFRefutation
% 0.83/1.01  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.83/1.01  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.83/1.01  fof(t40_subset_1, conjecture, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_tarski(X2,k3_subset_1(X1,X3)))=>X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 0.83/1.01  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.83/1.01  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.83/1.01  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.83/1.01  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 0.83/1.01  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.83/1.01  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.83/1.01  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.83/1.01  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.83/1.01  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.83/1.01  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.83/1.01  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.83/1.01  fof(c_0_14, plain, ![X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(X31))|k3_subset_1(X31,X32)=k4_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.83/1.01  fof(c_0_15, plain, ![X4, X5]:k4_xboole_0(X4,X5)=k5_xboole_0(X4,k3_xboole_0(X4,X5)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.83/1.01  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>((r1_tarski(X2,X3)&r1_tarski(X2,k3_subset_1(X1,X3)))=>X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t40_subset_1])).
% 0.83/1.01  cnf(c_0_17, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.83/1.01  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.83/1.01  fof(c_0_19, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&((r1_tarski(esk3_0,esk4_0)&r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0)))&esk3_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.83/1.01  fof(c_0_20, plain, ![X6, X7, X8]:((r1_tarski(X6,X7)|~r1_tarski(X6,k4_xboole_0(X7,X8)))&(r1_xboole_0(X6,X8)|~r1_tarski(X6,k4_xboole_0(X7,X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.83/1.01  cnf(c_0_21, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.83/1.01  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.83/1.01  fof(c_0_23, plain, ![X16, X17, X18]:(~r1_tarski(X16,X17)|r1_xboole_0(X16,k4_xboole_0(X18,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.83/1.01  fof(c_0_24, plain, ![X14, X15]:((~r1_xboole_0(X14,X15)|k4_xboole_0(X14,X15)=X14)&(k4_xboole_0(X14,X15)!=X14|r1_xboole_0(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.83/1.01  cnf(c_0_25, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.83/1.01  cnf(c_0_26, negated_conjecture, (r1_tarski(esk3_0,k3_subset_1(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.83/1.01  cnf(c_0_27, negated_conjecture, (k3_subset_1(esk2_0,esk4_0)=k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.83/1.01  cnf(c_0_28, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.83/1.01  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.83/1.01  cnf(c_0_30, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_25, c_0_18])).
% 0.83/1.01  cnf(c_0_31, negated_conjecture, (r1_tarski(esk3_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.83/1.01  fof(c_0_32, plain, ![X19, X20, X21]:(~r1_tarski(X19,X20)|~r1_xboole_0(X19,X21)|r1_tarski(X19,k4_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 0.83/1.01  cnf(c_0_33, plain, (r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_18])).
% 0.83/1.01  cnf(c_0_34, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.83/1.01  cnf(c_0_35, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_18])).
% 0.83/1.01  cnf(c_0_36, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.83/1.01  cnf(c_0_37, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.83/1.01  cnf(c_0_38, negated_conjecture, (r1_xboole_0(esk3_0,k5_xboole_0(X1,k3_xboole_0(X1,esk4_0)))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.83/1.01  cnf(c_0_39, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,esk4_0))=esk3_0), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.83/1.01  cnf(c_0_40, plain, (r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(rw,[status(thm)],[c_0_37, c_0_18])).
% 0.83/1.01  cnf(c_0_41, negated_conjecture, (r1_xboole_0(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.83/1.01  fof(c_0_42, plain, ![X22, X23, X24, X25, X26, X27]:(((~r2_hidden(X24,X23)|r1_tarski(X24,X22)|X23!=k1_zfmisc_1(X22))&(~r1_tarski(X25,X22)|r2_hidden(X25,X23)|X23!=k1_zfmisc_1(X22)))&((~r2_hidden(esk1_2(X26,X27),X27)|~r1_tarski(esk1_2(X26,X27),X26)|X27=k1_zfmisc_1(X26))&(r2_hidden(esk1_2(X26,X27),X27)|r1_tarski(esk1_2(X26,X27),X26)|X27=k1_zfmisc_1(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.83/1.01  cnf(c_0_43, negated_conjecture, (r1_tarski(esk3_0,k5_xboole_0(X1,k3_xboole_0(X1,esk3_0)))|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.83/1.01  cnf(c_0_44, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.83/1.01  cnf(c_0_45, negated_conjecture, (r1_tarski(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0)))), inference(spm,[status(thm)],[c_0_43, c_0_34])).
% 0.83/1.01  fof(c_0_46, plain, ![X29, X30]:(((~m1_subset_1(X30,X29)|r2_hidden(X30,X29)|v1_xboole_0(X29))&(~r2_hidden(X30,X29)|m1_subset_1(X30,X29)|v1_xboole_0(X29)))&((~m1_subset_1(X30,X29)|v1_xboole_0(X30)|~v1_xboole_0(X29))&(~v1_xboole_0(X30)|m1_subset_1(X30,X29)|~v1_xboole_0(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.83/1.01  cnf(c_0_47, negated_conjecture, (r2_hidden(esk3_0,X1)|X1!=k1_zfmisc_1(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0)))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.83/1.01  cnf(c_0_48, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.83/1.01  cnf(c_0_49, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0))))), inference(er,[status(thm)],[c_0_47])).
% 0.83/1.01  fof(c_0_50, plain, ![X10, X11]:(v1_xboole_0(X11)|(~r1_tarski(X11,X10)|~r1_xboole_0(X11,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.83/1.01  fof(c_0_51, plain, ![X12, X13]:r1_xboole_0(k4_xboole_0(X12,X13),X13), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.83/1.01  fof(c_0_52, plain, ![X9]:k4_xboole_0(X9,k1_xboole_0)=X9, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.83/1.01  cnf(c_0_53, plain, (m1_subset_1(X1,X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.83/1.01  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0))))|v1_xboole_0(k1_zfmisc_1(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0))))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.83/1.01  cnf(c_0_55, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.83/1.01  cnf(c_0_56, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.83/1.01  fof(c_0_57, plain, ![X35]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X35)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.83/1.01  cnf(c_0_58, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.83/1.01  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0))))|m1_subset_1(X1,k1_zfmisc_1(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0))))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.83/1.01  cnf(c_0_60, negated_conjecture, (v1_xboole_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_36]), c_0_34])])).
% 0.83/1.01  cnf(c_0_61, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_56, c_0_18])).
% 0.83/1.01  fof(c_0_62, plain, ![X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(X33))|k3_subset_1(X33,k3_subset_1(X33,X34))=X34), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.83/1.01  cnf(c_0_63, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.83/1.01  cnf(c_0_64, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_58, c_0_18])).
% 0.83/1.01  cnf(c_0_65, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0))))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.83/1.01  cnf(c_0_66, plain, (k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_35, c_0_61])).
% 0.83/1.01  cnf(c_0_67, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.83/1.01  cnf(c_0_68, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_63]), c_0_64])).
% 0.83/1.01  cnf(c_0_69, negated_conjecture, (k3_subset_1(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0)),esk3_0)=k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_65]), c_0_66])).
% 0.83/1.01  cnf(c_0_70, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_63]), c_0_68])).
% 0.83/1.01  cnf(c_0_71, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.83/1.01  cnf(c_0_72, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_65]), c_0_69]), c_0_70]), c_0_71]), ['proof']).
% 0.83/1.01  # SZS output end CNFRefutation
% 0.83/1.01  # Proof object total steps             : 73
% 0.83/1.01  # Proof object clause steps            : 44
% 0.83/1.01  # Proof object formula steps           : 29
% 0.83/1.01  # Proof object conjectures             : 23
% 0.83/1.01  # Proof object clause conjectures      : 20
% 0.83/1.01  # Proof object formula conjectures     : 3
% 0.83/1.01  # Proof object initial clauses used    : 18
% 0.83/1.01  # Proof object initial formulas used   : 14
% 0.83/1.01  # Proof object generating inferences   : 18
% 0.83/1.01  # Proof object simplifying inferences  : 16
% 0.83/1.01  # Training examples: 0 positive, 0 negative
% 0.83/1.01  # Parsed axioms                        : 14
% 0.83/1.01  # Removed by relevancy pruning/SinE    : 0
% 0.83/1.01  # Initial clauses                      : 25
% 0.83/1.01  # Removed in clause preprocessing      : 1
% 0.83/1.01  # Initial clauses in saturation        : 24
% 0.83/1.01  # Processed clauses                    : 3005
% 0.83/1.01  # ...of these trivial                  : 8
% 0.83/1.01  # ...subsumed                          : 1154
% 0.83/1.01  # ...remaining for further processing  : 1842
% 0.83/1.01  # Other redundant clauses eliminated   : 673
% 0.83/1.01  # Clauses deleted for lack of memory   : 0
% 0.83/1.01  # Backward-subsumed                    : 479
% 0.83/1.01  # Backward-rewritten                   : 220
% 0.83/1.01  # Generated clauses                    : 45945
% 0.83/1.01  # ...of the previous two non-trivial   : 42473
% 0.83/1.01  # Contextual simplify-reflections      : 28
% 0.83/1.01  # Paramodulations                      : 44844
% 0.83/1.01  # Factorizations                       : 144
% 0.83/1.01  # Equation resolutions                 : 957
% 0.83/1.01  # Propositional unsat checks           : 0
% 0.83/1.01  #    Propositional check models        : 0
% 0.83/1.01  #    Propositional check unsatisfiable : 0
% 0.83/1.01  #    Propositional clauses             : 0
% 0.83/1.01  #    Propositional clauses after purity: 0
% 0.83/1.01  #    Propositional unsat core size     : 0
% 0.83/1.01  #    Propositional preprocessing time  : 0.000
% 0.83/1.01  #    Propositional encoding time       : 0.000
% 0.83/1.01  #    Propositional solver time         : 0.000
% 0.83/1.01  #    Success case prop preproc time    : 0.000
% 0.83/1.01  #    Success case prop encoding time   : 0.000
% 0.83/1.01  #    Success case prop solver time     : 0.000
% 0.83/1.01  # Current number of processed clauses  : 1119
% 0.83/1.01  #    Positive orientable unit clauses  : 84
% 0.83/1.01  #    Positive unorientable unit clauses: 0
% 0.83/1.01  #    Negative unit clauses             : 1
% 0.83/1.01  #    Non-unit-clauses                  : 1034
% 0.83/1.01  # Current number of unprocessed clauses: 38405
% 0.83/1.01  # ...number of literals in the above   : 297782
% 0.83/1.01  # Current number of archived formulas  : 0
% 0.83/1.01  # Current number of archived clauses   : 724
% 0.83/1.01  # Clause-clause subsumption calls (NU) : 506318
% 0.83/1.01  # Rec. Clause-clause subsumption calls : 29252
% 0.83/1.01  # Non-unit clause-clause subsumptions  : 1598
% 0.83/1.01  # Unit Clause-clause subsumption calls : 3852
% 0.83/1.01  # Rewrite failures with RHS unbound    : 0
% 0.83/1.01  # BW rewrite match attempts            : 276
% 0.83/1.01  # BW rewrite match successes           : 49
% 0.83/1.01  # Condensation attempts                : 0
% 0.83/1.01  # Condensation successes               : 0
% 0.83/1.01  # Termbank termtop insertions          : 1205249
% 0.83/1.01  
% 0.83/1.01  # -------------------------------------------------
% 0.83/1.01  # User time                : 0.652 s
% 0.83/1.01  # System time              : 0.026 s
% 0.83/1.01  # Total time               : 0.678 s
% 0.83/1.01  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
