%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:40 EST 2020

% Result     : Theorem 0.42s
% Output     : CNFRefutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  139 (38917 expanded)
%              Number of clauses        :  116 (18184 expanded)
%              Number of leaves         :   11 (10320 expanded)
%              Depth                    :   28
%              Number of atoms          :  215 (66301 expanded)
%              Number of equality atoms :   86 (33189 expanded)
%              Maximal formula depth    :   13 (   2 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t34_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t31_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(c_0_11,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(X6,X7) != k1_xboole_0
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | k4_xboole_0(X6,X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_12,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_13,plain,(
    ! [X13] : k4_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_14,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | r1_tarski(k4_xboole_0(X12,X11),k4_xboole_0(X12,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X18,X17)
        | r1_tarski(X18,X16)
        | X17 != k1_zfmisc_1(X16) )
      & ( ~ r1_tarski(X19,X16)
        | r2_hidden(X19,X17)
        | X17 != k1_zfmisc_1(X16) )
      & ( ~ r2_hidden(esk1_2(X20,X21),X21)
        | ~ r1_tarski(esk1_2(X20,X21),X20)
        | X21 = k1_zfmisc_1(X20) )
      & ( r2_hidden(esk1_2(X20,X21),X21)
        | r1_tarski(esk1_2(X20,X21),X20)
        | X21 = k1_zfmisc_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_19,plain,
    ( r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r1_tarski(k5_xboole_0(X3,k3_xboole_0(X3,X2)),k5_xboole_0(X3,k3_xboole_0(X3,X1)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_16]),c_0_16])).

cnf(c_0_24,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21])])).

fof(c_0_25,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | k3_subset_1(X25,X26) = k4_xboole_0(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_26,plain,(
    ! [X23,X24] :
      ( ( ~ m1_subset_1(X24,X23)
        | r2_hidden(X24,X23)
        | v1_xboole_0(X23) )
      & ( ~ r2_hidden(X24,X23)
        | m1_subset_1(X24,X23)
        | v1_xboole_0(X23) )
      & ( ~ m1_subset_1(X24,X23)
        | v1_xboole_0(X24)
        | ~ v1_xboole_0(X23) )
      & ( ~ v1_xboole_0(X24)
        | m1_subset_1(X24,X23)
        | ~ v1_xboole_0(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_21]),c_0_21])).

fof(c_0_29,plain,(
    ! [X27] : ~ v1_xboole_0(k1_zfmisc_1(X27)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_30,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_31,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_16])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_38,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_24])).

fof(c_0_39,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_16]),c_0_16])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k3_subset_1(X1,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_38]),c_0_34])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(X1,X1))) = k3_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_42]),c_0_21])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X2,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_43])).

cnf(c_0_48,plain,
    ( k3_subset_1(X1,X1) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_21]),c_0_41])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_44,c_0_16])).

cnf(c_0_50,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_21])).

fof(c_0_51,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(X2,X3)
            <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_subset_1])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | k5_xboole_0(k1_xboole_0,k3_subset_1(X1,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( k3_subset_1(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_28]),c_0_41])).

cnf(c_0_54,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_50]),c_0_46])).

fof(c_0_55,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ( ~ r1_tarski(esk3_0,esk4_0)
      | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) )
    & ( r1_tarski(esk3_0,esk4_0)
      | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_51])])])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_54])])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_56]),c_0_21])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_34])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_64,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_40])).

cnf(c_0_65,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_43])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_63]),c_0_34])).

cnf(c_0_68,plain,
    ( r2_hidden(k3_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_64])).

cnf(c_0_69,plain,
    ( r2_hidden(k5_xboole_0(X1,k3_xboole_0(X2,X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_65])).

cnf(c_0_70,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_56])).

cnf(c_0_71,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)) = k3_subset_1(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_59])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_43])).

cnf(c_0_73,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_66]),c_0_43])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,k3_subset_1(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_21,c_0_48])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_67])).

cnf(c_0_76,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_68]),c_0_34])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_40])).

cnf(c_0_78,plain,
    ( m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X2,X1)),k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_69]),c_0_34])).

cnf(c_0_79,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_70]),c_0_34])).

cnf(c_0_80,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk3_0))) = k3_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_71])).

cnf(c_0_81,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_48]),c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0)) = k3_subset_1(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_63])).

cnf(c_0_83,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_75]),c_0_43])).

cnf(c_0_84,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_subset_1(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_76]),c_0_77])).

cnf(c_0_85,plain,
    ( k3_subset_1(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1))) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_78]),c_0_72])).

cnf(c_0_86,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_64]),c_0_43])).

cnf(c_0_87,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_79]),c_0_21])).

cnf(c_0_88,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk3_0))) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk3_0) = k3_subset_1(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_71,c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0))) = k3_xboole_0(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_82])).

cnf(c_0_91,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_83]),c_0_48]),c_0_74])).

cnf(c_0_92,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_subset_1(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_77,c_0_84])).

cnf(c_0_93,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk3_0)) = k3_subset_1(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_88]),c_0_81]),c_0_89])).

cnf(c_0_95,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_53]),c_0_21])).

cnf(c_0_96,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0))) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk4_0) = k3_subset_1(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_82,c_0_91])).

cnf(c_0_98,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_subset_1(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk3_0),esk2_0)
    | k5_xboole_0(k3_subset_1(esk2_0,esk3_0),k3_subset_1(esk2_0,esk3_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_94])).

cnf(c_0_100,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_53]),c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0)) = k3_subset_1(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_96]),c_0_91]),c_0_97])).

cnf(c_0_102,plain,
    ( r1_tarski(k3_subset_1(X1,k3_xboole_0(X1,X2)),k3_subset_1(X1,k3_xboole_0(X1,X3)))
    | ~ r1_tarski(X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_98]),c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_100])])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk4_0),esk2_0)
    | k5_xboole_0(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk4_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_101])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(k3_subset_1(X1,k3_xboole_0(X1,esk2_0)),k3_subset_1(X1,k3_xboole_0(X1,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_102,c_0_75])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_103])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_100])])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(k3_subset_1(X1,k3_xboole_0(X1,esk2_0)),k3_subset_1(X1,k3_xboole_0(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_105,c_0_43])).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_106]),c_0_34])).

cnf(c_0_110,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_subset_1(esk2_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_88,c_0_94])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_112,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk2_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_107])).

cnf(c_0_113,plain,
    ( k5_xboole_0(X1,k3_subset_1(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_40,c_0_84])).

cnf(c_0_114,plain,
    ( k3_subset_1(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_49,c_0_98])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(k3_subset_1(k3_xboole_0(esk4_0,X1),k3_xboole_0(esk2_0,k3_xboole_0(esk4_0,X1))),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_93]),c_0_43]),c_0_53])).

cnf(c_0_116,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_48,c_0_53])).

cnf(c_0_117,plain,
    ( r1_tarski(k3_subset_1(X1,k3_xboole_0(X1,X2)),k3_subset_1(X1,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_102,c_0_64])).

cnf(c_0_118,negated_conjecture,
    ( k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_109]),c_0_94]),c_0_110])).

cnf(c_0_119,negated_conjecture,
    ( k5_xboole_0(k3_subset_1(esk2_0,esk4_0),k3_xboole_0(k3_subset_1(esk2_0,esk3_0),k3_subset_1(esk2_0,esk4_0))) = k1_xboole_0
    | r1_tarski(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_111]),c_0_43])).

cnf(c_0_120,plain,
    ( k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_21,c_0_43])).

cnf(c_0_121,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_112]),c_0_34])).

cnf(c_0_122,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_96,c_0_101])).

cnf(c_0_123,plain,
    ( k5_xboole_0(X1,k3_subset_1(X1,k3_xboole_0(X2,X1))) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_113,c_0_43])).

cnf(c_0_124,negated_conjecture,
    ( k3_subset_1(k3_xboole_0(esk4_0,X1),k3_xboole_0(esk2_0,k3_xboole_0(esk4_0,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_116]),c_0_87])).

cnf(c_0_125,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_74,c_0_53])).

cnf(c_0_126,negated_conjecture,
    ( r1_tarski(esk3_0,k3_subset_1(esk2_0,k3_xboole_0(esk2_0,k3_xboole_0(k3_subset_1(esk2_0,esk3_0),X1)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_94]),c_0_118])).

cnf(c_0_127,negated_conjecture,
    ( k3_xboole_0(k3_subset_1(esk2_0,esk3_0),k3_subset_1(esk2_0,esk4_0)) = k3_subset_1(esk2_0,esk4_0)
    | r1_tarski(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_119]),c_0_43]),c_0_120])).

cnf(c_0_128,negated_conjecture,
    ( k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_121]),c_0_101]),c_0_122])).

cnf(c_0_129,negated_conjecture,
    ( k3_xboole_0(esk2_0,k3_xboole_0(esk4_0,X1)) = k3_xboole_0(esk4_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_125])).

cnf(c_0_130,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_101]),c_0_128])])).

cnf(c_0_131,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,k3_xboole_0(esk4_0,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_129]),c_0_91])).

cnf(c_0_132,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_43])).

cnf(c_0_133,negated_conjecture,
    ( k3_subset_1(esk3_0,k3_xboole_0(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_114,c_0_130])).

cnf(c_0_134,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0)
    | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_135,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,k3_xboole_0(X1,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_131,c_0_132])).

cnf(c_0_136,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_133]),c_0_125])).

cnf(c_0_137,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_134,c_0_130])])).

cnf(c_0_138,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_137]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:50:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.42/0.60  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 0.42/0.60  # and selection function SelectLargestOrientable.
% 0.42/0.60  #
% 0.42/0.60  # Preprocessing time       : 0.027 s
% 0.42/0.60  # Presaturation interreduction done
% 0.42/0.60  
% 0.42/0.60  # Proof found!
% 0.42/0.60  # SZS status Theorem
% 0.42/0.60  # SZS output start CNFRefutation
% 0.42/0.60  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.42/0.60  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.42/0.60  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.42/0.60  fof(t34_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_xboole_1)).
% 0.42/0.60  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.42/0.60  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.42/0.60  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.42/0.60  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.42/0.60  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.42/0.60  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.42/0.60  fof(t31_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 0.42/0.60  fof(c_0_11, plain, ![X6, X7]:((k4_xboole_0(X6,X7)!=k1_xboole_0|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|k4_xboole_0(X6,X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.42/0.60  fof(c_0_12, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.42/0.60  fof(c_0_13, plain, ![X13]:k4_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.42/0.60  fof(c_0_14, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|r1_tarski(k4_xboole_0(X12,X11),k4_xboole_0(X12,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).
% 0.42/0.60  cnf(c_0_15, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.42/0.60  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.42/0.60  cnf(c_0_17, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.42/0.60  fof(c_0_18, plain, ![X16, X17, X18, X19, X20, X21]:(((~r2_hidden(X18,X17)|r1_tarski(X18,X16)|X17!=k1_zfmisc_1(X16))&(~r1_tarski(X19,X16)|r2_hidden(X19,X17)|X17!=k1_zfmisc_1(X16)))&((~r2_hidden(esk1_2(X20,X21),X21)|~r1_tarski(esk1_2(X20,X21),X20)|X21=k1_zfmisc_1(X20))&(r2_hidden(esk1_2(X20,X21),X21)|r1_tarski(esk1_2(X20,X21),X20)|X21=k1_zfmisc_1(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.42/0.60  cnf(c_0_19, plain, (r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.42/0.60  cnf(c_0_20, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.42/0.60  cnf(c_0_21, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_17, c_0_16])).
% 0.42/0.60  cnf(c_0_22, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.42/0.60  cnf(c_0_23, plain, (r1_tarski(k5_xboole_0(X3,k3_xboole_0(X3,X2)),k5_xboole_0(X3,k3_xboole_0(X3,X1)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_16]), c_0_16])).
% 0.42/0.60  cnf(c_0_24, plain, (r1_tarski(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21])])).
% 0.42/0.60  fof(c_0_25, plain, ![X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(X25))|k3_subset_1(X25,X26)=k4_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.42/0.60  fof(c_0_26, plain, ![X23, X24]:(((~m1_subset_1(X24,X23)|r2_hidden(X24,X23)|v1_xboole_0(X23))&(~r2_hidden(X24,X23)|m1_subset_1(X24,X23)|v1_xboole_0(X23)))&((~m1_subset_1(X24,X23)|v1_xboole_0(X24)|~v1_xboole_0(X23))&(~v1_xboole_0(X24)|m1_subset_1(X24,X23)|~v1_xboole_0(X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.42/0.60  cnf(c_0_27, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_22])).
% 0.42/0.60  cnf(c_0_28, plain, (r1_tarski(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_21]), c_0_21])).
% 0.42/0.60  fof(c_0_29, plain, ![X27]:~v1_xboole_0(k1_zfmisc_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.42/0.60  fof(c_0_30, plain, ![X14, X15]:k4_xboole_0(X14,k4_xboole_0(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.42/0.60  cnf(c_0_31, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.42/0.60  cnf(c_0_32, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.42/0.60  cnf(c_0_33, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.42/0.60  cnf(c_0_34, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.42/0.60  cnf(c_0_35, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.42/0.60  cnf(c_0_36, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_31, c_0_16])).
% 0.42/0.60  cnf(c_0_37, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.42/0.60  cnf(c_0_38, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_27, c_0_24])).
% 0.42/0.60  fof(c_0_39, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.42/0.60  cnf(c_0_40, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_16]), c_0_16])).
% 0.42/0.60  cnf(c_0_41, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k3_subset_1(X1,X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.42/0.60  cnf(c_0_42, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_38]), c_0_34])).
% 0.42/0.60  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.42/0.60  cnf(c_0_44, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.42/0.60  cnf(c_0_45, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(X1,X1)))=k3_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.42/0.60  cnf(c_0_46, plain, (k3_subset_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_42]), c_0_21])).
% 0.42/0.60  cnf(c_0_47, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X2,X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_43])).
% 0.42/0.60  cnf(c_0_48, plain, (k3_subset_1(X1,X1)=k3_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_21]), c_0_41])).
% 0.42/0.60  cnf(c_0_49, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_44, c_0_16])).
% 0.42/0.60  cnf(c_0_50, plain, (k3_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_21])).
% 0.42/0.60  fof(c_0_51, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t31_subset_1])).
% 0.42/0.60  cnf(c_0_52, plain, (r1_tarski(k1_xboole_0,X1)|k5_xboole_0(k1_xboole_0,k3_subset_1(X1,X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.42/0.60  cnf(c_0_53, plain, (k3_subset_1(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_28]), c_0_41])).
% 0.42/0.60  cnf(c_0_54, plain, (k5_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_50]), c_0_46])).
% 0.42/0.60  fof(c_0_55, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&((~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))&(r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_51])])])).
% 0.42/0.60  cnf(c_0_56, plain, (r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_54])])).
% 0.42/0.60  cnf(c_0_57, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.42/0.60  cnf(c_0_58, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.42/0.60  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.42/0.60  cnf(c_0_60, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_56]), c_0_21])).
% 0.42/0.60  cnf(c_0_61, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_57])).
% 0.42/0.60  cnf(c_0_62, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_34])).
% 0.42/0.60  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.42/0.60  cnf(c_0_64, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_60, c_0_40])).
% 0.42/0.60  cnf(c_0_65, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1)), inference(spm,[status(thm)],[c_0_60, c_0_43])).
% 0.42/0.60  cnf(c_0_66, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.42/0.60  cnf(c_0_67, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_63]), c_0_34])).
% 0.42/0.60  cnf(c_0_68, plain, (r2_hidden(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_27, c_0_64])).
% 0.42/0.60  cnf(c_0_69, plain, (r2_hidden(k5_xboole_0(X1,k3_xboole_0(X2,X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_27, c_0_65])).
% 0.42/0.60  cnf(c_0_70, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_27, c_0_56])).
% 0.42/0.60  cnf(c_0_71, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))=k3_subset_1(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_59])).
% 0.42/0.60  cnf(c_0_72, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1))))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_40, c_0_43])).
% 0.42/0.60  cnf(c_0_73, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_66]), c_0_43])).
% 0.42/0.60  cnf(c_0_74, plain, (k5_xboole_0(X1,k3_subset_1(X1,X1))=X1), inference(spm,[status(thm)],[c_0_21, c_0_48])).
% 0.42/0.60  cnf(c_0_75, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_61, c_0_67])).
% 0.42/0.60  cnf(c_0_76, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_68]), c_0_34])).
% 0.42/0.60  cnf(c_0_77, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_40, c_0_40])).
% 0.42/0.60  cnf(c_0_78, plain, (m1_subset_1(k5_xboole_0(X1,k3_xboole_0(X2,X1)),k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_69]), c_0_34])).
% 0.42/0.60  cnf(c_0_79, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_70]), c_0_34])).
% 0.42/0.60  cnf(c_0_80, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk3_0)))=k3_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_40, c_0_71])).
% 0.42/0.60  cnf(c_0_81, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_48]), c_0_74])).
% 0.42/0.60  cnf(c_0_82, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk4_0))=k3_subset_1(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_63])).
% 0.42/0.60  cnf(c_0_83, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_75]), c_0_43])).
% 0.42/0.60  cnf(c_0_84, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_subset_1(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_76]), c_0_77])).
% 0.42/0.60  cnf(c_0_85, plain, (k3_subset_1(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1)))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_78]), c_0_72])).
% 0.42/0.60  cnf(c_0_86, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_64]), c_0_43])).
% 0.42/0.60  cnf(c_0_87, plain, (k3_subset_1(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_79]), c_0_21])).
% 0.42/0.60  cnf(c_0_88, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk3_0)))=esk3_0), inference(rw,[status(thm)],[c_0_80, c_0_81])).
% 0.42/0.60  cnf(c_0_89, negated_conjecture, (k5_xboole_0(esk2_0,esk3_0)=k3_subset_1(esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_71, c_0_81])).
% 0.42/0.60  cnf(c_0_90, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0)))=k3_xboole_0(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_82])).
% 0.42/0.60  cnf(c_0_91, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_83]), c_0_48]), c_0_74])).
% 0.42/0.60  cnf(c_0_92, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_subset_1(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_77, c_0_84])).
% 0.42/0.60  cnf(c_0_93, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87])).
% 0.42/0.60  cnf(c_0_94, negated_conjecture, (k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk3_0))=k3_subset_1(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_88]), c_0_81]), c_0_89])).
% 0.42/0.60  cnf(c_0_95, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_53]), c_0_21])).
% 0.42/0.60  cnf(c_0_96, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0)))=esk4_0), inference(rw,[status(thm)],[c_0_90, c_0_91])).
% 0.42/0.60  cnf(c_0_97, negated_conjecture, (k5_xboole_0(esk2_0,esk4_0)=k3_subset_1(esk2_0,esk4_0)), inference(rw,[status(thm)],[c_0_82, c_0_91])).
% 0.42/0.60  cnf(c_0_98, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k3_subset_1(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_92, c_0_93])).
% 0.42/0.60  cnf(c_0_99, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk3_0),esk2_0)|k5_xboole_0(k3_subset_1(esk2_0,esk3_0),k3_subset_1(esk2_0,esk3_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_94])).
% 0.42/0.60  cnf(c_0_100, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_53]), c_0_95])).
% 0.42/0.60  cnf(c_0_101, negated_conjecture, (k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0))=k3_subset_1(esk2_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_96]), c_0_91]), c_0_97])).
% 0.42/0.60  cnf(c_0_102, plain, (r1_tarski(k3_subset_1(X1,k3_xboole_0(X1,X2)),k3_subset_1(X1,k3_xboole_0(X1,X3)))|~r1_tarski(X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_98]), c_0_98])).
% 0.42/0.60  cnf(c_0_103, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_100])])).
% 0.42/0.60  cnf(c_0_104, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk4_0),esk2_0)|k5_xboole_0(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk4_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_101])).
% 0.42/0.60  cnf(c_0_105, negated_conjecture, (r1_tarski(k3_subset_1(X1,k3_xboole_0(X1,esk2_0)),k3_subset_1(X1,k3_xboole_0(X1,esk4_0)))), inference(spm,[status(thm)],[c_0_102, c_0_75])).
% 0.42/0.60  cnf(c_0_106, negated_conjecture, (r2_hidden(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_27, c_0_103])).
% 0.42/0.60  cnf(c_0_107, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_100])])).
% 0.42/0.60  cnf(c_0_108, negated_conjecture, (r1_tarski(k3_subset_1(X1,k3_xboole_0(X1,esk2_0)),k3_subset_1(X1,k3_xboole_0(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_105, c_0_43])).
% 0.42/0.60  cnf(c_0_109, negated_conjecture, (m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_106]), c_0_34])).
% 0.42/0.60  cnf(c_0_110, negated_conjecture, (k5_xboole_0(esk2_0,k3_subset_1(esk2_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[c_0_88, c_0_94])).
% 0.42/0.60  cnf(c_0_111, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.42/0.60  cnf(c_0_112, negated_conjecture, (r2_hidden(k3_subset_1(esk2_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_27, c_0_107])).
% 0.42/0.60  cnf(c_0_113, plain, (k5_xboole_0(X1,k3_subset_1(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_40, c_0_84])).
% 0.42/0.60  cnf(c_0_114, plain, (k3_subset_1(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_49, c_0_98])).
% 0.42/0.60  cnf(c_0_115, negated_conjecture, (r1_tarski(k3_subset_1(k3_xboole_0(esk4_0,X1),k3_xboole_0(esk2_0,k3_xboole_0(esk4_0,X1))),k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_93]), c_0_43]), c_0_53])).
% 0.42/0.60  cnf(c_0_116, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_48, c_0_53])).
% 0.42/0.60  cnf(c_0_117, plain, (r1_tarski(k3_subset_1(X1,k3_xboole_0(X1,X2)),k3_subset_1(X1,k3_xboole_0(X1,k3_xboole_0(X2,X3))))), inference(spm,[status(thm)],[c_0_102, c_0_64])).
% 0.42/0.60  cnf(c_0_118, negated_conjecture, (k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_109]), c_0_94]), c_0_110])).
% 0.42/0.60  cnf(c_0_119, negated_conjecture, (k5_xboole_0(k3_subset_1(esk2_0,esk4_0),k3_xboole_0(k3_subset_1(esk2_0,esk3_0),k3_subset_1(esk2_0,esk4_0)))=k1_xboole_0|r1_tarski(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_111]), c_0_43])).
% 0.42/0.60  cnf(c_0_120, plain, (k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_21, c_0_43])).
% 0.42/0.60  cnf(c_0_121, negated_conjecture, (m1_subset_1(k3_subset_1(esk2_0,esk4_0),k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_112]), c_0_34])).
% 0.42/0.60  cnf(c_0_122, negated_conjecture, (k5_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0))=esk4_0), inference(rw,[status(thm)],[c_0_96, c_0_101])).
% 0.42/0.60  cnf(c_0_123, plain, (k5_xboole_0(X1,k3_subset_1(X1,k3_xboole_0(X2,X1)))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_113, c_0_43])).
% 0.42/0.60  cnf(c_0_124, negated_conjecture, (k3_subset_1(k3_xboole_0(esk4_0,X1),k3_xboole_0(esk2_0,k3_xboole_0(esk4_0,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_116]), c_0_87])).
% 0.42/0.60  cnf(c_0_125, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_74, c_0_53])).
% 0.42/0.60  cnf(c_0_126, negated_conjecture, (r1_tarski(esk3_0,k3_subset_1(esk2_0,k3_xboole_0(esk2_0,k3_xboole_0(k3_subset_1(esk2_0,esk3_0),X1))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_94]), c_0_118])).
% 0.42/0.60  cnf(c_0_127, negated_conjecture, (k3_xboole_0(k3_subset_1(esk2_0,esk3_0),k3_subset_1(esk2_0,esk4_0))=k3_subset_1(esk2_0,esk4_0)|r1_tarski(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_119]), c_0_43]), c_0_120])).
% 0.42/0.60  cnf(c_0_128, negated_conjecture, (k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk4_0))=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_121]), c_0_101]), c_0_122])).
% 0.42/0.60  cnf(c_0_129, negated_conjecture, (k3_xboole_0(esk2_0,k3_xboole_0(esk4_0,X1))=k3_xboole_0(esk4_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_124]), c_0_125])).
% 0.42/0.60  cnf(c_0_130, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_101]), c_0_128])])).
% 0.42/0.60  cnf(c_0_131, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,k3_xboole_0(esk4_0,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_129]), c_0_91])).
% 0.42/0.60  cnf(c_0_132, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_93, c_0_43])).
% 0.42/0.60  cnf(c_0_133, negated_conjecture, (k3_subset_1(esk3_0,k3_xboole_0(esk3_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_114, c_0_130])).
% 0.42/0.60  cnf(c_0_134, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.42/0.60  cnf(c_0_135, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,k3_xboole_0(X1,esk4_0)))), inference(spm,[status(thm)],[c_0_131, c_0_132])).
% 0.42/0.60  cnf(c_0_136, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_133]), c_0_125])).
% 0.42/0.60  cnf(c_0_137, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_134, c_0_130])])).
% 0.42/0.60  cnf(c_0_138, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_136]), c_0_137]), ['proof']).
% 0.42/0.60  # SZS output end CNFRefutation
% 0.42/0.60  # Proof object total steps             : 139
% 0.42/0.60  # Proof object clause steps            : 116
% 0.42/0.60  # Proof object formula steps           : 23
% 0.42/0.60  # Proof object conjectures             : 52
% 0.42/0.60  # Proof object clause conjectures      : 49
% 0.42/0.60  # Proof object formula conjectures     : 3
% 0.42/0.60  # Proof object initial clauses used    : 17
% 0.42/0.60  # Proof object initial formulas used   : 11
% 0.42/0.60  # Proof object generating inferences   : 72
% 0.42/0.60  # Proof object simplifying inferences  : 89
% 0.42/0.60  # Training examples: 0 positive, 0 negative
% 0.42/0.60  # Parsed axioms                        : 11
% 0.42/0.60  # Removed by relevancy pruning/SinE    : 0
% 0.42/0.60  # Initial clauses                      : 21
% 0.42/0.60  # Removed in clause preprocessing      : 1
% 0.42/0.60  # Initial clauses in saturation        : 20
% 0.42/0.60  # Processed clauses                    : 1870
% 0.42/0.60  # ...of these trivial                  : 286
% 0.42/0.60  # ...subsumed                          : 919
% 0.42/0.60  # ...remaining for further processing  : 665
% 0.42/0.60  # Other redundant clauses eliminated   : 278
% 0.42/0.60  # Clauses deleted for lack of memory   : 0
% 0.42/0.60  # Backward-subsumed                    : 6
% 0.42/0.60  # Backward-rewritten                   : 283
% 0.42/0.60  # Generated clauses                    : 18405
% 0.42/0.60  # ...of the previous two non-trivial   : 15373
% 0.42/0.60  # Contextual simplify-reflections      : 0
% 0.42/0.60  # Paramodulations                      : 18125
% 0.42/0.60  # Factorizations                       : 2
% 0.42/0.60  # Equation resolutions                 : 278
% 0.42/0.60  # Propositional unsat checks           : 0
% 0.42/0.60  #    Propositional check models        : 0
% 0.42/0.60  #    Propositional check unsatisfiable : 0
% 0.42/0.60  #    Propositional clauses             : 0
% 0.42/0.60  #    Propositional clauses after purity: 0
% 0.42/0.60  #    Propositional unsat core size     : 0
% 0.42/0.60  #    Propositional preprocessing time  : 0.000
% 0.42/0.60  #    Propositional encoding time       : 0.000
% 0.42/0.60  #    Propositional solver time         : 0.000
% 0.42/0.60  #    Success case prop preproc time    : 0.000
% 0.42/0.60  #    Success case prop encoding time   : 0.000
% 0.42/0.60  #    Success case prop solver time     : 0.000
% 0.42/0.60  # Current number of processed clauses  : 352
% 0.42/0.60  #    Positive orientable unit clauses  : 191
% 0.42/0.60  #    Positive unorientable unit clauses: 1
% 0.42/0.60  #    Negative unit clauses             : 2
% 0.42/0.60  #    Non-unit-clauses                  : 158
% 0.42/0.60  # Current number of unprocessed clauses: 13210
% 0.42/0.60  # ...number of literals in the above   : 70706
% 0.42/0.60  # Current number of archived formulas  : 0
% 0.42/0.60  # Current number of archived clauses   : 310
% 0.42/0.60  # Clause-clause subsumption calls (NU) : 30882
% 0.42/0.60  # Rec. Clause-clause subsumption calls : 13337
% 0.42/0.60  # Non-unit clause-clause subsumptions  : 853
% 0.42/0.60  # Unit Clause-clause subsumption calls : 3529
% 0.42/0.60  # Rewrite failures with RHS unbound    : 0
% 0.42/0.60  # BW rewrite match attempts            : 350
% 0.42/0.60  # BW rewrite match successes           : 68
% 0.42/0.60  # Condensation attempts                : 0
% 0.42/0.60  # Condensation successes               : 0
% 0.42/0.60  # Termbank termtop insertions          : 372075
% 0.42/0.60  
% 0.42/0.60  # -------------------------------------------------
% 0.42/0.60  # User time                : 0.245 s
% 0.42/0.60  # System time              : 0.015 s
% 0.42/0.60  # Total time               : 0.261 s
% 0.42/0.60  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
