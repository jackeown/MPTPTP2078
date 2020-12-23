%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:59 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  101 (3321 expanded)
%              Number of clauses        :   82 (1537 expanded)
%              Number of leaves         :    9 ( 834 expanded)
%              Depth                    :   24
%              Number of atoms          :  187 (6922 expanded)
%              Number of equality atoms :   75 (4361 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t57_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
     => ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
        | ( X1 = X5
          & X2 = X6
          & X3 = X7
          & X4 = X8 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(fc3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X2)
     => v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t139_zfmisc_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2,X3,X4] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
            | r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X4,X3)) )
         => r1_tarski(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(fc4_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(rc1_xboole_0,axiom,(
    ? [X1] : v1_xboole_0(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
       => ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
          | ( X1 = X5
            & X2 = X6
            & X3 = X7
            & X4 = X8 ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_mcart_1])).

fof(c_0_10,plain,(
    ! [X26,X27,X28,X29] : k4_zfmisc_1(X26,X27,X28,X29) = k2_zfmisc_1(k3_zfmisc_1(X26,X27,X28),X29) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X23,X24,X25] : k3_zfmisc_1(X23,X24,X25) = k2_zfmisc_1(k2_zfmisc_1(X23,X24),X25) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_12,negated_conjecture,
    ( k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0) = k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0)
    & k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0) != k1_xboole_0
    & ( esk2_0 != esk6_0
      | esk3_0 != esk7_0
      | esk4_0 != esk8_0
      | esk5_0 != esk9_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_13,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X13,X14] :
      ( ~ v1_xboole_0(X14)
      | v1_xboole_0(k2_zfmisc_1(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).

cnf(c_0_16,negated_conjecture,
    ( k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0) = k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_18,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(X9)
      | X9 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_19,plain,
    ( v1_xboole_0(k2_zfmisc_1(X2,X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0),esk9_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_22,plain,(
    ! [X17,X18,X19,X20] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X17,X18),k2_zfmisc_1(X19,X20))
        | r1_tarski(X18,X20)
        | v1_xboole_0(X17) )
      & ( ~ r1_tarski(k2_zfmisc_1(X18,X17),k2_zfmisc_1(X20,X19))
        | r1_tarski(X18,X20)
        | v1_xboole_0(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t139_zfmisc_1])])])])])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0))
    | ~ v1_xboole_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_21,c_0_17])).

fof(c_0_26,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_27,plain,(
    ! [X15,X16] :
      ( ~ v1_xboole_0(X15)
      | v1_xboole_0(k2_zfmisc_1(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_zfmisc_1])])).

fof(c_0_28,plain,(
    v1_xboole_0(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X3)
    | v1_xboole_0(X2)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_xboole_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0),X1)
    | ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0),k2_zfmisc_1(X1,X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_20]),c_0_30])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_32])).

cnf(c_0_38,plain,
    ( esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_33])).

cnf(c_0_39,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0),k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))
    | v1_xboole_0(X2)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_20])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_37]),c_0_25])).

cnf(c_0_44,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)
    | ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_35]),c_0_42])).

cnf(c_0_47,plain,
    ( r1_tarski(X2,X4)
    | v1_xboole_0(X1)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_37]),c_0_44])])).

cnf(c_0_49,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk8_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_40]),c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(X1,esk8_0)
    | v1_xboole_0(X2)
    | ~ r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_37]),c_0_44])])).

cnf(c_0_54,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0) = k2_zfmisc_1(k1_xboole_0,esk9_0)
    | ~ v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_36])).

cnf(c_0_55,negated_conjecture,
    ( esk8_0 = esk4_0
    | ~ r1_tarski(esk4_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk4_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_35]),c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( k2_zfmisc_1(k1_xboole_0,esk9_0) != k1_xboole_0
    | ~ v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( esk8_0 = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_37]),c_0_44])])).

cnf(c_0_60,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk4_0) = k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( k2_zfmisc_1(k1_xboole_0,esk5_0) != k1_xboole_0
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_36])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk6_0,esk7_0),k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_40]),c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk6_0,esk7_0))
    | v1_xboole_0(X2)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_37]),c_0_44])])).

cnf(c_0_65,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk7_0) = k2_zfmisc_1(esk2_0,esk3_0)
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_35]),c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk4_0),esk5_0) != k1_xboole_0
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_37])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_37]),c_0_44])])).

cnf(c_0_69,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk7_0) = k2_zfmisc_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66])])).

cnf(c_0_70,negated_conjecture,
    ( k2_zfmisc_1(k1_xboole_0,esk5_0) != k1_xboole_0
    | ~ v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_37]),c_0_44])])).

cnf(c_0_71,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk9_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_20,c_0_49])).

cnf(c_0_72,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk8_0),esk9_0)
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_36])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(esk7_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_62]),c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(X1,esk7_0)
    | v1_xboole_0(X2)
    | ~ r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_37]),c_0_44])])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(esk9_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0),k2_zfmisc_1(X2,X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_71]),c_0_50])).

cnf(c_0_77,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk8_0),esk9_0) != k1_xboole_0
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( esk7_0 = esk3_0
    | ~ r1_tarski(esk3_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(esk3_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_35]),c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk9_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_35])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(X1,esk9_0)
    | v1_xboole_0(X2)
    | ~ r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_71])).

cnf(c_0_82,negated_conjecture,
    ( k2_zfmisc_1(k1_xboole_0,esk9_0) != k1_xboole_0
    | ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_37]),c_0_44])])).

cnf(c_0_83,negated_conjecture,
    ( esk7_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79])])).

cnf(c_0_84,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk4_0),esk5_0) != k1_xboole_0
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_36])).

cnf(c_0_85,negated_conjecture,
    ( esk2_0 != esk6_0
    | esk3_0 != esk7_0
    | esk4_0 != esk8_0
    | esk5_0 != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_86,negated_conjecture,
    ( esk9_0 = esk5_0
    | ~ r1_tarski(esk5_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(esk5_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_35]),c_0_50])).

cnf(c_0_88,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_37]),c_0_44])])).

cnf(c_0_89,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk3_0) = k2_zfmisc_1(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_69,c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( k2_zfmisc_1(k1_xboole_0,esk5_0) != k1_xboole_0
    | ~ v1_xboole_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_37]),c_0_44])])).

cnf(c_0_91,negated_conjecture,
    ( esk6_0 != esk2_0
    | esk7_0 != esk3_0
    | esk9_0 != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_58])])).

cnf(c_0_92,negated_conjecture,
    ( esk9_0 = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87])])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(esk6_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_62]),c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(X1,esk6_0)
    | v1_xboole_0(X2)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_37]),c_0_44])])).

cnf(c_0_96,negated_conjecture,
    ( esk6_0 != esk2_0
    | esk7_0 != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_92])])).

cnf(c_0_97,negated_conjecture,
    ( esk6_0 = esk2_0
    | ~ r1_tarski(esk2_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(esk2_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_35]),c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( esk6_0 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_83])])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_98])]),c_0_99]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:26:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.027 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t57_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(k4_zfmisc_1(X1,X2,X3,X4)=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_mcart_1)).
% 0.12/0.38  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.12/0.38  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.12/0.38  fof(fc3_zfmisc_1, axiom, ![X1, X2]:(v1_xboole_0(X2)=>v1_xboole_0(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 0.12/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.12/0.38  fof(t139_zfmisc_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2, X3, X4]:((r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))|r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X4,X3)))=>r1_tarski(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 0.12/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.38  fof(fc4_zfmisc_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>v1_xboole_0(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 0.12/0.38  fof(rc1_xboole_0, axiom, ?[X1]:v1_xboole_0(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 0.12/0.38  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(k4_zfmisc_1(X1,X2,X3,X4)=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8)))), inference(assume_negation,[status(cth)],[t57_mcart_1])).
% 0.12/0.38  fof(c_0_10, plain, ![X26, X27, X28, X29]:k4_zfmisc_1(X26,X27,X28,X29)=k2_zfmisc_1(k3_zfmisc_1(X26,X27,X28),X29), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.12/0.38  fof(c_0_11, plain, ![X23, X24, X25]:k3_zfmisc_1(X23,X24,X25)=k2_zfmisc_1(k2_zfmisc_1(X23,X24),X25), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.12/0.38  fof(c_0_12, negated_conjecture, (k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0)=k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0)&(k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0)!=k1_xboole_0&(esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0|esk5_0!=esk9_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.12/0.38  cnf(c_0_13, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_14, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  fof(c_0_15, plain, ![X13, X14]:(~v1_xboole_0(X14)|v1_xboole_0(k2_zfmisc_1(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).
% 0.12/0.38  cnf(c_0_16, negated_conjecture, (k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0)=k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_17, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.38  fof(c_0_18, plain, ![X9]:(~v1_xboole_0(X9)|X9=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.12/0.38  cnf(c_0_19, plain, (v1_xboole_0(k2_zfmisc_1(X2,X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_20, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0),esk9_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_17])).
% 0.12/0.38  cnf(c_0_21, negated_conjecture, (k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  fof(c_0_22, plain, ![X17, X18, X19, X20]:((~r1_tarski(k2_zfmisc_1(X17,X18),k2_zfmisc_1(X19,X20))|r1_tarski(X18,X20)|v1_xboole_0(X17))&(~r1_tarski(k2_zfmisc_1(X18,X17),k2_zfmisc_1(X20,X19))|r1_tarski(X18,X20)|v1_xboole_0(X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t139_zfmisc_1])])])])])).
% 0.12/0.38  cnf(c_0_23, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, (v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0))|~v1_xboole_0(esk9_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_21, c_0_17])).
% 0.12/0.38  fof(c_0_26, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.38  fof(c_0_27, plain, ![X15, X16]:(~v1_xboole_0(X15)|v1_xboole_0(k2_zfmisc_1(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_zfmisc_1])])).
% 0.12/0.38  fof(c_0_28, plain, v1_xboole_0(esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).
% 0.12/0.38  cnf(c_0_29, plain, (r1_tarski(X1,X3)|v1_xboole_0(X2)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (~v1_xboole_0(esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.12/0.38  cnf(c_0_31, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.38  cnf(c_0_32, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.38  cnf(c_0_33, plain, (v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.38  cnf(c_0_34, negated_conjecture, (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0),X1)|~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0),k2_zfmisc_1(X1,X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_20]), c_0_30])).
% 0.12/0.38  cnf(c_0_35, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_31])).
% 0.12/0.38  cnf(c_0_36, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_23, c_0_19])).
% 0.12/0.38  cnf(c_0_37, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_23, c_0_32])).
% 0.12/0.38  cnf(c_0_38, plain, (esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_33])).
% 0.12/0.38  cnf(c_0_39, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.38  cnf(c_0_40, negated_conjecture, (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0),k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.12/0.38  cnf(c_0_41, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))|v1_xboole_0(X2)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_29, c_0_20])).
% 0.12/0.38  cnf(c_0_42, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_25, c_0_36])).
% 0.12/0.38  cnf(c_0_43, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_37]), c_0_25])).
% 0.12/0.38  cnf(c_0_44, plain, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_33, c_0_38])).
% 0.12/0.38  cnf(c_0_45, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)|~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.12/0.38  cnf(c_0_46, negated_conjecture, (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_35]), c_0_42])).
% 0.12/0.38  cnf(c_0_47, plain, (r1_tarski(X2,X4)|v1_xboole_0(X1)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_48, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_37]), c_0_44])])).
% 0.12/0.38  cnf(c_0_49, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46])])).
% 0.12/0.38  cnf(c_0_50, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))), inference(spm,[status(thm)],[c_0_25, c_0_37])).
% 0.12/0.38  cnf(c_0_51, negated_conjecture, (r1_tarski(esk8_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_40]), c_0_48])).
% 0.12/0.38  cnf(c_0_52, negated_conjecture, (r1_tarski(X1,esk8_0)|v1_xboole_0(X2)|~r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))), inference(spm,[status(thm)],[c_0_47, c_0_49])).
% 0.12/0.38  cnf(c_0_53, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_37]), c_0_44])])).
% 0.12/0.38  cnf(c_0_54, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0)=k2_zfmisc_1(k1_xboole_0,esk9_0)|~v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_20, c_0_36])).
% 0.12/0.38  cnf(c_0_55, negated_conjecture, (esk8_0=esk4_0|~r1_tarski(esk4_0,esk8_0)), inference(spm,[status(thm)],[c_0_39, c_0_51])).
% 0.12/0.38  cnf(c_0_56, negated_conjecture, (r1_tarski(esk4_0,esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_35]), c_0_53])).
% 0.12/0.38  cnf(c_0_57, negated_conjecture, (k2_zfmisc_1(k1_xboole_0,esk9_0)!=k1_xboole_0|~v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_25, c_0_54])).
% 0.12/0.38  cnf(c_0_58, negated_conjecture, (esk8_0=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56])])).
% 0.12/0.38  cnf(c_0_59, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_37]), c_0_44])])).
% 0.12/0.38  cnf(c_0_60, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk4_0)=k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[c_0_49, c_0_58])).
% 0.12/0.38  cnf(c_0_61, negated_conjecture, (k2_zfmisc_1(k1_xboole_0,esk5_0)!=k1_xboole_0|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_36])).
% 0.12/0.38  cnf(c_0_62, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk6_0,esk7_0),k2_zfmisc_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_40]), c_0_59])).
% 0.12/0.38  cnf(c_0_63, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk6_0,esk7_0))|v1_xboole_0(X2)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))), inference(spm,[status(thm)],[c_0_29, c_0_60])).
% 0.12/0.38  cnf(c_0_64, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_37]), c_0_44])])).
% 0.12/0.38  cnf(c_0_65, negated_conjecture, (k2_zfmisc_1(esk6_0,esk7_0)=k2_zfmisc_1(esk2_0,esk3_0)|~r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_39, c_0_62])).
% 0.12/0.38  cnf(c_0_66, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),k2_zfmisc_1(esk6_0,esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_35]), c_0_64])).
% 0.12/0.38  cnf(c_0_67, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk4_0),esk5_0)!=k1_xboole_0|~v1_xboole_0(esk2_0)), inference(spm,[status(thm)],[c_0_25, c_0_37])).
% 0.12/0.38  cnf(c_0_68, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_37]), c_0_44])])).
% 0.12/0.38  cnf(c_0_69, negated_conjecture, (k2_zfmisc_1(esk6_0,esk7_0)=k2_zfmisc_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66])])).
% 0.12/0.38  cnf(c_0_70, negated_conjecture, (k2_zfmisc_1(k1_xboole_0,esk5_0)!=k1_xboole_0|~v1_xboole_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_37]), c_0_44])])).
% 0.12/0.38  cnf(c_0_71, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk9_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0)), inference(rw,[status(thm)],[c_0_20, c_0_49])).
% 0.12/0.38  cnf(c_0_72, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0)=k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk8_0),esk9_0)|~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_20, c_0_36])).
% 0.12/0.38  cnf(c_0_73, negated_conjecture, (r1_tarski(esk7_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_62]), c_0_68])).
% 0.12/0.38  cnf(c_0_74, negated_conjecture, (r1_tarski(X1,esk7_0)|v1_xboole_0(X2)|~r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_47, c_0_69])).
% 0.12/0.38  cnf(c_0_75, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_37]), c_0_44])])).
% 0.12/0.38  cnf(c_0_76, negated_conjecture, (r1_tarski(esk9_0,X1)|~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0),k2_zfmisc_1(X2,X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_71]), c_0_50])).
% 0.12/0.38  cnf(c_0_77, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk8_0),esk9_0)!=k1_xboole_0|~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_25, c_0_72])).
% 0.12/0.38  cnf(c_0_78, negated_conjecture, (esk7_0=esk3_0|~r1_tarski(esk3_0,esk7_0)), inference(spm,[status(thm)],[c_0_39, c_0_73])).
% 0.12/0.38  cnf(c_0_79, negated_conjecture, (r1_tarski(esk3_0,esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_35]), c_0_75])).
% 0.12/0.38  cnf(c_0_80, negated_conjecture, (r1_tarski(esk9_0,esk5_0)), inference(spm,[status(thm)],[c_0_76, c_0_35])).
% 0.12/0.38  cnf(c_0_81, negated_conjecture, (r1_tarski(X1,esk9_0)|v1_xboole_0(X2)|~r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_47, c_0_71])).
% 0.12/0.38  cnf(c_0_82, negated_conjecture, (k2_zfmisc_1(k1_xboole_0,esk9_0)!=k1_xboole_0|~v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_37]), c_0_44])])).
% 0.12/0.38  cnf(c_0_83, negated_conjecture, (esk7_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_79])])).
% 0.12/0.38  cnf(c_0_84, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk4_0),esk5_0)!=k1_xboole_0|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_36])).
% 0.12/0.38  cnf(c_0_85, negated_conjecture, (esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0|esk5_0!=esk9_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_86, negated_conjecture, (esk9_0=esk5_0|~r1_tarski(esk5_0,esk9_0)), inference(spm,[status(thm)],[c_0_39, c_0_80])).
% 0.12/0.38  cnf(c_0_87, negated_conjecture, (r1_tarski(esk5_0,esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_35]), c_0_50])).
% 0.12/0.38  cnf(c_0_88, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_37]), c_0_44])])).
% 0.12/0.38  cnf(c_0_89, negated_conjecture, (k2_zfmisc_1(esk6_0,esk3_0)=k2_zfmisc_1(esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_69, c_0_83])).
% 0.12/0.38  cnf(c_0_90, negated_conjecture, (k2_zfmisc_1(k1_xboole_0,esk5_0)!=k1_xboole_0|~v1_xboole_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_37]), c_0_44])])).
% 0.12/0.38  cnf(c_0_91, negated_conjecture, (esk6_0!=esk2_0|esk7_0!=esk3_0|esk9_0!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_58])])).
% 0.12/0.38  cnf(c_0_92, negated_conjecture, (esk9_0=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87])])).
% 0.12/0.38  cnf(c_0_93, negated_conjecture, (r1_tarski(esk6_0,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_62]), c_0_88])).
% 0.12/0.38  cnf(c_0_94, negated_conjecture, (r1_tarski(X1,esk6_0)|v1_xboole_0(X2)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_29, c_0_89])).
% 0.12/0.38  cnf(c_0_95, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_37]), c_0_44])])).
% 0.12/0.38  cnf(c_0_96, negated_conjecture, (esk6_0!=esk2_0|esk7_0!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_92])])).
% 0.12/0.38  cnf(c_0_97, negated_conjecture, (esk6_0=esk2_0|~r1_tarski(esk2_0,esk6_0)), inference(spm,[status(thm)],[c_0_39, c_0_93])).
% 0.12/0.38  cnf(c_0_98, negated_conjecture, (r1_tarski(esk2_0,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_35]), c_0_95])).
% 0.12/0.38  cnf(c_0_99, negated_conjecture, (esk6_0!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_83])])).
% 0.12/0.38  cnf(c_0_100, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_98])]), c_0_99]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 101
% 0.12/0.38  # Proof object clause steps            : 82
% 0.12/0.38  # Proof object formula steps           : 19
% 0.12/0.38  # Proof object conjectures             : 69
% 0.12/0.38  # Proof object clause conjectures      : 66
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 13
% 0.12/0.38  # Proof object initial formulas used   : 9
% 0.12/0.38  # Proof object generating inferences   : 52
% 0.12/0.38  # Proof object simplifying inferences  : 64
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 10
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 15
% 0.12/0.38  # Removed in clause preprocessing      : 2
% 0.12/0.38  # Initial clauses in saturation        : 13
% 0.12/0.38  # Processed clauses                    : 549
% 0.12/0.38  # ...of these trivial                  : 4
% 0.12/0.38  # ...subsumed                          : 396
% 0.12/0.38  # ...remaining for further processing  : 149
% 0.12/0.38  # Other redundant clauses eliminated   : 2
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 15
% 0.12/0.38  # Backward-rewritten                   : 64
% 0.12/0.38  # Generated clauses                    : 755
% 0.12/0.38  # ...of the previous two non-trivial   : 671
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 753
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 2
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 56
% 0.12/0.38  #    Positive orientable unit clauses  : 12
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 10
% 0.12/0.38  #    Non-unit-clauses                  : 34
% 0.12/0.38  # Current number of unprocessed clauses: 21
% 0.12/0.38  # ...number of literals in the above   : 69
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 93
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 975
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 892
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 84
% 0.12/0.38  # Unit Clause-clause subsumption calls : 251
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 20
% 0.12/0.38  # BW rewrite match successes           : 20
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 10552
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.040 s
% 0.12/0.38  # System time              : 0.006 s
% 0.12/0.38  # Total time               : 0.046 s
% 0.12/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
