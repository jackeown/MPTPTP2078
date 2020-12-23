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
% DateTime   : Thu Dec  3 10:59:59 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  144 (12555 expanded)
%              Number of clauses        :  119 (5956 expanded)
%              Number of leaves         :   12 (3134 expanded)
%              Depth                    :   40
%              Number of atoms          :  352 (24929 expanded)
%              Number of equality atoms :  181 (14398 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(rc1_xboole_0,axiom,(
    ? [X1] : v1_xboole_0(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(t139_zfmisc_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2,X3,X4] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
            | r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X4,X3)) )
         => r1_tarski(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(fc4_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(fc3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X2)
     => v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(t193_relat_1,axiom,(
    ! [X1,X2] : r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
       => ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
          | ( X1 = X5
            & X2 = X6
            & X3 = X7
            & X4 = X8 ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_mcart_1])).

fof(c_0_13,plain,(
    ! [X29,X30,X31,X32] : k4_zfmisc_1(X29,X30,X31,X32) = k2_zfmisc_1(k3_zfmisc_1(X29,X30,X31),X32) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X26,X27,X28] : k3_zfmisc_1(X26,X27,X28) = k2_zfmisc_1(k2_zfmisc_1(X26,X27),X28) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_15,negated_conjecture,
    ( k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0) = k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0)
    & k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0) != k1_xboole_0
    & ( esk2_0 != esk6_0
      | esk3_0 != esk7_0
      | esk4_0 != esk8_0
      | esk5_0 != esk9_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_16,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(X9)
      | X9 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_19,plain,(
    v1_xboole_0(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).

fof(c_0_20,plain,(
    ! [X17,X18,X19,X20] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X17,X18),k2_zfmisc_1(X19,X20))
        | r1_tarski(X18,X20)
        | v1_xboole_0(X17) )
      & ( ~ r1_tarski(k2_zfmisc_1(X18,X17),k2_zfmisc_1(X20,X19))
        | r1_tarski(X18,X20)
        | v1_xboole_0(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t139_zfmisc_1])])])])])).

cnf(c_0_21,negated_conjecture,
    ( k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0) = k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_23,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(X2,X4)
    | v1_xboole_0(X1)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0),esk9_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_22])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X15,X16] :
      ( ~ v1_xboole_0(X15)
      | v1_xboole_0(k2_zfmisc_1(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_zfmisc_1])])).

cnf(c_0_30,plain,
    ( esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(X1,esk9_0)
    | v1_xboole_0(X2)
    | ~ r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_30])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X3)
    | v1_xboole_0(X2)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk5_0,esk9_0)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk9_0,X1)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))
    | ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0),k2_zfmisc_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0),X1)
    | v1_xboole_0(esk9_0)
    | ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0),k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_22])).

cnf(c_0_42,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0) = k1_xboole_0
    | r1_tarski(esk5_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_37])).

cnf(c_0_43,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk9_0,esk5_0)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_32])).

fof(c_0_45,plain,(
    ! [X13,X14] :
      ( ~ v1_xboole_0(X14)
      | v1_xboole_0(k2_zfmisc_1(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))
    | v1_xboole_0(X2)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_27])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0),k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))
    | v1_xboole_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_32])).

cnf(c_0_48,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk5_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_50,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k1_xboole_0
    | r1_tarski(esk9_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_44])).

cnf(c_0_51,plain,
    ( v1_xboole_0(k2_zfmisc_1(X2,X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))
    | v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_32])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk8_0,esk4_0)
    | v1_xboole_0(k2_zfmisc_1(esk6_0,esk7_0))
    | v1_xboole_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( esk9_0 = esk5_0
    | ~ r1_tarski(esk9_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk9_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_50]),c_0_43]),c_0_41])).

fof(c_0_56,plain,(
    ! [X23,X24] : r1_tarski(k1_relat_1(k2_zfmisc_1(X23,X24)),X23) ),
    inference(variable_rename,[status(thm)],[t193_relat_1])).

cnf(c_0_57,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_34])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk4_0,esk8_0)
    | v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0))
    | v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk7_0) = k1_xboole_0
    | r1_tarski(esk8_0,esk4_0)
    | v1_xboole_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( esk9_0 = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k1_xboole_0
    | r1_tarski(esk4_0,esk8_0)
    | v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk7_0) = k1_xboole_0
    | r1_tarski(esk8_0,esk4_0)
    | v1_xboole_0(esk5_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X2)
    | v1_xboole_0(X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X3),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k1_xboole_0
    | r1_tarski(esk4_0,esk8_0)
    | v1_xboole_0(k2_zfmisc_1(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk7_0) = k1_xboole_0
    | r1_tarski(esk8_0,esk4_0)
    | v1_xboole_0(k2_zfmisc_1(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_64])).

cnf(c_0_69,plain,
    ( X1 = k1_relat_1(k1_xboole_0)
    | ~ r1_tarski(X1,k1_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_65])).

cnf(c_0_70,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | v1_xboole_0(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_43]),c_0_32])])).

cnf(c_0_71,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k1_xboole_0
    | k2_zfmisc_1(esk5_0,X1) = k1_xboole_0
    | r1_tarski(esk4_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0),esk5_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_60])).

cnf(c_0_73,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk7_0) = k1_xboole_0
    | k2_zfmisc_1(X1,esk5_0) = k1_xboole_0
    | r1_tarski(esk8_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_68])).

cnf(c_0_74,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k1_xboole_0
    | k2_zfmisc_1(esk5_0,X1) = k1_xboole_0
    | esk8_0 = esk4_0
    | ~ r1_tarski(esk8_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk7_0) = k1_xboole_0
    | r1_tarski(esk8_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_41])).

cnf(c_0_77,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | X1 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk7_0) = k1_xboole_0
    | k2_zfmisc_1(esk2_0,esk3_0) = k1_xboole_0
    | k2_zfmisc_1(esk5_0,X1) = k1_xboole_0
    | esk8_0 = esk4_0 ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_79,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k1_xboole_0
    | k2_zfmisc_1(esk5_0,X1) = k1_xboole_0
    | esk8_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_78]),c_0_43]),c_0_43]),c_0_41])).

cnf(c_0_81,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[c_0_65,c_0_79])).

cnf(c_0_82,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_79]),c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k1_xboole_0
    | esk8_0 = esk4_0
    | r1_tarski(X1,X2)
    | v1_xboole_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_80]),c_0_81])])).

cnf(c_0_84,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | r1_tarski(esk4_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_63])).

cnf(c_0_85,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k1_xboole_0
    | esk8_0 = esk4_0
    | X1 = k1_xboole_0
    | v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk8_0 = esk4_0
    | ~ r1_tarski(esk8_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk7_0) = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | r1_tarski(esk8_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_59])).

cnf(c_0_88,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k1_xboole_0
    | esk8_0 = esk4_0
    | v1_xboole_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_85]),c_0_43]),c_0_41])).

fof(c_0_89,plain,(
    ! [X25] :
      ( ~ v1_relat_1(X25)
      | r1_tarski(X25,k2_zfmisc_1(k1_relat_1(X25),k2_relat_1(X25))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

fof(c_0_90,plain,(
    ! [X21,X22] : v1_relat_1(k2_zfmisc_1(X21,X22)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_91,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk7_0) = k1_xboole_0
    | k2_zfmisc_1(esk2_0,esk3_0) = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | esk8_0 = esk4_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k1_xboole_0
    | esk8_0 = esk4_0
    | v1_xboole_0(k2_zfmisc_1(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_88])).

cnf(c_0_93,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_94,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)
    | v1_xboole_0(esk5_0)
    | ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0),k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_52])).

cnf(c_0_96,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk8_0 = esk4_0
    | esk9_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_91]),c_0_43]),c_0_43]),c_0_41])).

cnf(c_0_97,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k1_xboole_0
    | k2_zfmisc_1(X1,esk5_0) = k1_xboole_0
    | esk8_0 = esk4_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_92])).

cnf(c_0_98,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X1,X2)),k2_relat_1(k2_zfmisc_1(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)
    | v1_xboole_0(esk9_0)
    | v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_47])).

cnf(c_0_100,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | esk8_0 = esk4_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_96]),c_0_43]),c_0_43])])).

cnf(c_0_101,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = k1_xboole_0
    | esk8_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_97]),c_0_41])).

cnf(c_0_102,plain,
    ( r1_tarski(X1,k1_relat_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)
    | v1_xboole_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_60])])).

cnf(c_0_104,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk8_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_100]),c_0_62]),c_0_41])).

cnf(c_0_105,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0),k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))
    | v1_xboole_0(esk5_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_60])).

cnf(c_0_106,negated_conjecture,
    ( esk8_0 = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_101]),c_0_43]),c_0_43])])).

cnf(c_0_107,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | v1_xboole_0(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_102]),c_0_61])])).

cnf(c_0_108,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk4_0) = k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)
    | esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_24])).

cnf(c_0_109,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))
    | v1_xboole_0(esk5_0) ),
    inference(rw,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_110,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)) = k2_zfmisc_1(esk6_0,esk7_0)
    | esk5_0 = k1_xboole_0
    | v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk6_0,esk7_0),k2_zfmisc_1(esk2_0,esk3_0))
    | v1_xboole_0(esk5_0)
    | v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_109])).

cnf(c_0_112,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk7_0) = k2_zfmisc_1(esk2_0,esk3_0)
    | esk5_0 = k1_xboole_0
    | v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_107,c_0_110])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(esk7_0,esk3_0)
    | v1_xboole_0(esk4_0)
    | v1_xboole_0(esk5_0)
    | v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_111])).

cnf(c_0_114,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk7_0) = k2_zfmisc_1(esk2_0,esk3_0)
    | esk5_0 = k1_xboole_0
    | v1_xboole_0(k2_zfmisc_1(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_112])).

cnf(c_0_115,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk7_0,esk3_0)
    | v1_xboole_0(esk5_0)
    | v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_113])).

cnf(c_0_116,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk4_0),esk5_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_72,c_0_106])).

cnf(c_0_117,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk7_0) = k2_zfmisc_1(esk2_0,esk3_0)
    | k2_zfmisc_1(X1,esk4_0) = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_114])).

cnf(c_0_118,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk7_0,esk3_0)
    | v1_xboole_0(k2_zfmisc_1(X1,esk5_0))
    | v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_115])).

cnf(c_0_119,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk7_0) = k2_zfmisc_1(esk2_0,esk3_0)
    | esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_43]),c_0_41])).

cnf(c_0_120,negated_conjecture,
    ( k2_zfmisc_1(X1,esk5_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r1_tarski(esk7_0,esk3_0)
    | v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_118])).

cnf(c_0_121,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(esk2_0,esk3_0)) = esk6_0
    | esk5_0 = k1_xboole_0
    | v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_107,c_0_119])).

cnf(c_0_122,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk7_0,esk3_0)
    | v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_120])).

cnf(c_0_123,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk6_0 = esk2_0
    | v1_xboole_0(esk7_0)
    | v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_107,c_0_121])).

cnf(c_0_124,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk7_0,esk3_0)
    | v1_xboole_0(k2_zfmisc_1(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_122])).

cnf(c_0_125,negated_conjecture,
    ( esk2_0 != esk6_0
    | esk3_0 != esk7_0
    | esk4_0 != esk8_0
    | esk5_0 != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_126,negated_conjecture,
    ( esk6_0 = esk2_0
    | esk5_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_123])).

cnf(c_0_127,negated_conjecture,
    ( k2_zfmisc_1(X1,esk4_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | r1_tarski(esk7_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_124])).

cnf(c_0_128,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(X1,esk7_0)
    | v1_xboole_0(X2)
    | ~ r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_119])).

cnf(c_0_129,negated_conjecture,
    ( esk6_0 != esk2_0
    | esk7_0 != esk3_0
    | esk8_0 != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_125,c_0_60])])).

cnf(c_0_130,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk6_0 = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_126])).

cnf(c_0_131,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk7_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_127]),c_0_43]),c_0_41])).

cnf(c_0_132,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(esk3_0,esk7_0)
    | v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_128,c_0_32])).

cnf(c_0_133,negated_conjecture,
    ( esk6_0 != esk2_0
    | esk7_0 != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129,c_0_106])])).

cnf(c_0_134,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk6_0 = esk2_0
    | esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_130]),c_0_62]),c_0_43]),c_0_43]),c_0_41])).

cnf(c_0_135,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 = esk3_0
    | ~ r1_tarski(esk3_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_131])).

cnf(c_0_136,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | r1_tarski(esk3_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_132])).

cnf(c_0_137,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk7_0 != esk3_0 ),
    inference(spm,[status(thm)],[c_0_133,c_0_134])).

cnf(c_0_138,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk7_0 = esk3_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_135,c_0_136])).

cnf(c_0_139,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_140,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_139]),c_0_43]),c_0_43]),c_0_43]),c_0_41])).

cnf(c_0_141,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_140]),c_0_62])])).

cnf(c_0_142,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_141]),c_0_62]),c_0_43]),c_0_43])])).

cnf(c_0_143,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_142]),c_0_43]),c_0_43]),c_0_43])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:11:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.20/0.41  # and selection function SelectCQIArNpEqFirst.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.026 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t57_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(k4_zfmisc_1(X1,X2,X3,X4)=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_mcart_1)).
% 0.20/0.41  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.20/0.41  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.20/0.41  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.41  fof(rc1_xboole_0, axiom, ?[X1]:v1_xboole_0(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 0.20/0.41  fof(t139_zfmisc_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2, X3, X4]:((r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))|r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X4,X3)))=>r1_tarski(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 0.20/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.41  fof(fc4_zfmisc_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>v1_xboole_0(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 0.20/0.41  fof(fc3_zfmisc_1, axiom, ![X1, X2]:(v1_xboole_0(X2)=>v1_xboole_0(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 0.20/0.41  fof(t193_relat_1, axiom, ![X1, X2]:r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_relat_1)).
% 0.20/0.41  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 0.20/0.41  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.41  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(k4_zfmisc_1(X1,X2,X3,X4)=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8)))), inference(assume_negation,[status(cth)],[t57_mcart_1])).
% 0.20/0.41  fof(c_0_13, plain, ![X29, X30, X31, X32]:k4_zfmisc_1(X29,X30,X31,X32)=k2_zfmisc_1(k3_zfmisc_1(X29,X30,X31),X32), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.20/0.41  fof(c_0_14, plain, ![X26, X27, X28]:k3_zfmisc_1(X26,X27,X28)=k2_zfmisc_1(k2_zfmisc_1(X26,X27),X28), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.20/0.41  fof(c_0_15, negated_conjecture, (k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0)=k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0)&(k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0)!=k1_xboole_0&(esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0|esk5_0!=esk9_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.20/0.41  cnf(c_0_16, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_17, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  fof(c_0_18, plain, ![X9]:(~v1_xboole_0(X9)|X9=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.41  fof(c_0_19, plain, v1_xboole_0(esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).
% 0.20/0.41  fof(c_0_20, plain, ![X17, X18, X19, X20]:((~r1_tarski(k2_zfmisc_1(X17,X18),k2_zfmisc_1(X19,X20))|r1_tarski(X18,X20)|v1_xboole_0(X17))&(~r1_tarski(k2_zfmisc_1(X18,X17),k2_zfmisc_1(X20,X19))|r1_tarski(X18,X20)|v1_xboole_0(X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t139_zfmisc_1])])])])])).
% 0.20/0.41  cnf(c_0_21, negated_conjecture, (k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0)=k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_22, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.41  fof(c_0_23, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.41  cnf(c_0_24, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_25, plain, (v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  cnf(c_0_26, plain, (r1_tarski(X2,X4)|v1_xboole_0(X1)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_27, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0),esk9_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_22])).
% 0.20/0.41  cnf(c_0_28, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  fof(c_0_29, plain, ![X15, X16]:(~v1_xboole_0(X15)|v1_xboole_0(k2_zfmisc_1(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_zfmisc_1])])).
% 0.20/0.41  cnf(c_0_30, plain, (esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.41  cnf(c_0_31, negated_conjecture, (r1_tarski(X1,esk9_0)|v1_xboole_0(X2)|~r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.41  cnf(c_0_32, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_28])).
% 0.20/0.41  cnf(c_0_33, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.41  cnf(c_0_34, plain, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_25, c_0_30])).
% 0.20/0.41  cnf(c_0_35, plain, (r1_tarski(X1,X3)|v1_xboole_0(X2)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_36, negated_conjecture, (k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (r1_tarski(esk5_0,esk9_0)|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.41  cnf(c_0_38, plain, (v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.41  cnf(c_0_39, negated_conjecture, (r1_tarski(esk9_0,X1)|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))|~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0),k2_zfmisc_1(X2,X1))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.41  cnf(c_0_40, negated_conjecture, (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0),X1)|v1_xboole_0(esk9_0)|~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0),k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_35, c_0_27])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_36, c_0_22])).
% 0.20/0.41  cnf(c_0_42, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)=k1_xboole_0|r1_tarski(esk5_0,esk9_0)), inference(spm,[status(thm)],[c_0_24, c_0_37])).
% 0.20/0.41  cnf(c_0_43, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_38])).
% 0.20/0.41  cnf(c_0_44, negated_conjecture, (r1_tarski(esk9_0,esk5_0)|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_39, c_0_32])).
% 0.20/0.41  fof(c_0_45, plain, ![X13, X14]:(~v1_xboole_0(X14)|v1_xboole_0(k2_zfmisc_1(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).
% 0.20/0.41  cnf(c_0_46, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))|v1_xboole_0(X2)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_35, c_0_27])).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0),k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))|v1_xboole_0(esk9_0)), inference(spm,[status(thm)],[c_0_40, c_0_32])).
% 0.20/0.41  cnf(c_0_48, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  cnf(c_0_49, negated_conjecture, (r1_tarski(esk5_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])])).
% 0.20/0.41  cnf(c_0_50, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k1_xboole_0|r1_tarski(esk9_0,esk5_0)), inference(spm,[status(thm)],[c_0_24, c_0_44])).
% 0.20/0.41  cnf(c_0_51, plain, (v1_xboole_0(k2_zfmisc_1(X2,X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))|v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_46, c_0_32])).
% 0.20/0.41  cnf(c_0_53, negated_conjecture, (r1_tarski(esk8_0,esk4_0)|v1_xboole_0(k2_zfmisc_1(esk6_0,esk7_0))|v1_xboole_0(esk9_0)), inference(spm,[status(thm)],[c_0_26, c_0_47])).
% 0.20/0.41  cnf(c_0_54, negated_conjecture, (esk9_0=esk5_0|~r1_tarski(esk9_0,esk5_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.41  cnf(c_0_55, negated_conjecture, (r1_tarski(esk9_0,esk5_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_50]), c_0_43]), c_0_41])).
% 0.20/0.41  fof(c_0_56, plain, ![X23, X24]:r1_tarski(k1_relat_1(k2_zfmisc_1(X23,X24)),X23), inference(variable_rename,[status(thm)],[t193_relat_1])).
% 0.20/0.41  cnf(c_0_57, plain, (v1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_51, c_0_34])).
% 0.20/0.41  cnf(c_0_58, negated_conjecture, (r1_tarski(esk4_0,esk8_0)|v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0))|v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_26, c_0_52])).
% 0.20/0.41  cnf(c_0_59, negated_conjecture, (k2_zfmisc_1(esk6_0,esk7_0)=k1_xboole_0|r1_tarski(esk8_0,esk4_0)|v1_xboole_0(esk9_0)), inference(spm,[status(thm)],[c_0_24, c_0_53])).
% 0.20/0.41  cnf(c_0_60, negated_conjecture, (esk9_0=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])])).
% 0.20/0.41  cnf(c_0_61, plain, (r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.41  cnf(c_0_62, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_57])).
% 0.20/0.41  cnf(c_0_63, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k1_xboole_0|r1_tarski(esk4_0,esk8_0)|v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_24, c_0_58])).
% 0.20/0.41  cnf(c_0_64, negated_conjecture, (k2_zfmisc_1(esk6_0,esk7_0)=k1_xboole_0|r1_tarski(esk8_0,esk4_0)|v1_xboole_0(esk5_0)), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.41  cnf(c_0_65, plain, (r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.41  cnf(c_0_66, plain, (r1_tarski(X1,X2)|v1_xboole_0(X3)|~r1_tarski(k2_zfmisc_1(X1,X3),k1_xboole_0)), inference(spm,[status(thm)],[c_0_35, c_0_62])).
% 0.20/0.41  cnf(c_0_67, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k1_xboole_0|r1_tarski(esk4_0,esk8_0)|v1_xboole_0(k2_zfmisc_1(esk5_0,X1))), inference(spm,[status(thm)],[c_0_33, c_0_63])).
% 0.20/0.41  cnf(c_0_68, negated_conjecture, (k2_zfmisc_1(esk6_0,esk7_0)=k1_xboole_0|r1_tarski(esk8_0,esk4_0)|v1_xboole_0(k2_zfmisc_1(X1,esk5_0))), inference(spm,[status(thm)],[c_0_51, c_0_64])).
% 0.20/0.41  cnf(c_0_69, plain, (X1=k1_relat_1(k1_xboole_0)|~r1_tarski(X1,k1_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_48, c_0_65])).
% 0.20/0.41  cnf(c_0_70, plain, (r1_tarski(k1_xboole_0,X1)|v1_xboole_0(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_43]), c_0_32])])).
% 0.20/0.41  cnf(c_0_71, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k1_xboole_0|k2_zfmisc_1(esk5_0,X1)=k1_xboole_0|r1_tarski(esk4_0,esk8_0)), inference(spm,[status(thm)],[c_0_24, c_0_67])).
% 0.20/0.41  cnf(c_0_72, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0),esk5_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0)), inference(rw,[status(thm)],[c_0_27, c_0_60])).
% 0.20/0.41  cnf(c_0_73, negated_conjecture, (k2_zfmisc_1(esk6_0,esk7_0)=k1_xboole_0|k2_zfmisc_1(X1,esk5_0)=k1_xboole_0|r1_tarski(esk8_0,esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_68])).
% 0.20/0.41  cnf(c_0_74, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.41  cnf(c_0_75, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k1_xboole_0|k2_zfmisc_1(esk5_0,X1)=k1_xboole_0|esk8_0=esk4_0|~r1_tarski(esk8_0,esk4_0)), inference(spm,[status(thm)],[c_0_48, c_0_71])).
% 0.20/0.41  cnf(c_0_76, negated_conjecture, (k2_zfmisc_1(esk6_0,esk7_0)=k1_xboole_0|r1_tarski(esk8_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_41])).
% 0.20/0.41  cnf(c_0_77, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0|X1=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_74])).
% 0.20/0.41  cnf(c_0_78, negated_conjecture, (k2_zfmisc_1(esk6_0,esk7_0)=k1_xboole_0|k2_zfmisc_1(esk2_0,esk3_0)=k1_xboole_0|k2_zfmisc_1(esk5_0,X1)=k1_xboole_0|esk8_0=esk4_0), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.41  cnf(c_0_79, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(ef,[status(thm)],[c_0_77])).
% 0.20/0.41  cnf(c_0_80, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k1_xboole_0|k2_zfmisc_1(esk5_0,X1)=k1_xboole_0|esk8_0=esk4_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_78]), c_0_43]), c_0_43]), c_0_41])).
% 0.20/0.41  cnf(c_0_81, plain, (r1_tarski(k1_xboole_0,X1)), inference(rw,[status(thm)],[c_0_65, c_0_79])).
% 0.20/0.41  cnf(c_0_82, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_79]), c_0_79])).
% 0.20/0.41  cnf(c_0_83, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k1_xboole_0|esk8_0=esk4_0|r1_tarski(X1,X2)|v1_xboole_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_80]), c_0_81])])).
% 0.20/0.41  cnf(c_0_84, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k1_xboole_0|esk5_0=k1_xboole_0|r1_tarski(esk4_0,esk8_0)), inference(spm,[status(thm)],[c_0_24, c_0_63])).
% 0.20/0.41  cnf(c_0_85, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k1_xboole_0|esk8_0=esk4_0|X1=k1_xboole_0|v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.20/0.41  cnf(c_0_86, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k1_xboole_0|esk5_0=k1_xboole_0|esk8_0=esk4_0|~r1_tarski(esk8_0,esk4_0)), inference(spm,[status(thm)],[c_0_48, c_0_84])).
% 0.20/0.41  cnf(c_0_87, negated_conjecture, (k2_zfmisc_1(esk6_0,esk7_0)=k1_xboole_0|esk9_0=k1_xboole_0|r1_tarski(esk8_0,esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_59])).
% 0.20/0.41  cnf(c_0_88, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k1_xboole_0|esk8_0=esk4_0|v1_xboole_0(esk5_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_85]), c_0_43]), c_0_41])).
% 0.20/0.41  fof(c_0_89, plain, ![X25]:(~v1_relat_1(X25)|r1_tarski(X25,k2_zfmisc_1(k1_relat_1(X25),k2_relat_1(X25)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.20/0.41  fof(c_0_90, plain, ![X21, X22]:v1_relat_1(k2_zfmisc_1(X21,X22)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.41  cnf(c_0_91, negated_conjecture, (k2_zfmisc_1(esk6_0,esk7_0)=k1_xboole_0|k2_zfmisc_1(esk2_0,esk3_0)=k1_xboole_0|esk9_0=k1_xboole_0|esk8_0=esk4_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.20/0.41  cnf(c_0_92, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k1_xboole_0|esk8_0=esk4_0|v1_xboole_0(k2_zfmisc_1(X1,esk5_0))), inference(spm,[status(thm)],[c_0_51, c_0_88])).
% 0.20/0.41  cnf(c_0_93, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.20/0.41  cnf(c_0_94, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.20/0.41  cnf(c_0_95, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)|v1_xboole_0(esk5_0)|~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0),k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))), inference(spm,[status(thm)],[c_0_48, c_0_52])).
% 0.20/0.41  cnf(c_0_96, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k1_xboole_0|esk5_0=k1_xboole_0|esk8_0=esk4_0|esk9_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_91]), c_0_43]), c_0_43]), c_0_41])).
% 0.20/0.41  cnf(c_0_97, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k1_xboole_0|k2_zfmisc_1(X1,esk5_0)=k1_xboole_0|esk8_0=esk4_0), inference(spm,[status(thm)],[c_0_24, c_0_92])).
% 0.20/0.41  cnf(c_0_98, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X1,X2)),k2_relat_1(k2_zfmisc_1(X1,X2))))), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.20/0.41  cnf(c_0_99, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)|v1_xboole_0(esk9_0)|v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_95, c_0_47])).
% 0.20/0.41  cnf(c_0_100, negated_conjecture, (esk9_0=k1_xboole_0|esk8_0=esk4_0|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_96]), c_0_43]), c_0_43])])).
% 0.20/0.41  cnf(c_0_101, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=k1_xboole_0|esk8_0=esk4_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_97]), c_0_41])).
% 0.20/0.41  cnf(c_0_102, plain, (r1_tarski(X1,k1_relat_1(k2_zfmisc_1(X1,X2)))|v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_35, c_0_98])).
% 0.20/0.41  cnf(c_0_103, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)|v1_xboole_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_60])])).
% 0.20/0.41  cnf(c_0_104, negated_conjecture, (esk5_0=k1_xboole_0|esk8_0=esk4_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_100]), c_0_62]), c_0_41])).
% 0.20/0.41  cnf(c_0_105, negated_conjecture, (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0),k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))|v1_xboole_0(esk5_0)), inference(rw,[status(thm)],[c_0_47, c_0_60])).
% 0.20/0.41  cnf(c_0_106, negated_conjecture, (esk8_0=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_101]), c_0_43]), c_0_43])])).
% 0.20/0.41  cnf(c_0_107, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=X1|v1_xboole_0(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_102]), c_0_61])])).
% 0.20/0.41  cnf(c_0_108, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk4_0)=k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)|esk5_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_24])).
% 0.20/0.41  cnf(c_0_109, negated_conjecture, (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))|v1_xboole_0(esk5_0)), inference(rw,[status(thm)],[c_0_105, c_0_106])).
% 0.20/0.41  cnf(c_0_110, negated_conjecture, (k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))=k2_zfmisc_1(esk6_0,esk7_0)|esk5_0=k1_xboole_0|v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 0.20/0.41  cnf(c_0_111, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk6_0,esk7_0),k2_zfmisc_1(esk2_0,esk3_0))|v1_xboole_0(esk5_0)|v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_35, c_0_109])).
% 0.20/0.41  cnf(c_0_112, negated_conjecture, (k2_zfmisc_1(esk6_0,esk7_0)=k2_zfmisc_1(esk2_0,esk3_0)|esk5_0=k1_xboole_0|v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_107, c_0_110])).
% 0.20/0.41  cnf(c_0_113, negated_conjecture, (r1_tarski(esk7_0,esk3_0)|v1_xboole_0(esk4_0)|v1_xboole_0(esk5_0)|v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_111])).
% 0.20/0.41  cnf(c_0_114, negated_conjecture, (k2_zfmisc_1(esk6_0,esk7_0)=k2_zfmisc_1(esk2_0,esk3_0)|esk5_0=k1_xboole_0|v1_xboole_0(k2_zfmisc_1(X1,esk4_0))), inference(spm,[status(thm)],[c_0_51, c_0_112])).
% 0.20/0.41  cnf(c_0_115, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk7_0,esk3_0)|v1_xboole_0(esk5_0)|v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_113])).
% 0.20/0.41  cnf(c_0_116, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk4_0),esk5_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0)), inference(rw,[status(thm)],[c_0_72, c_0_106])).
% 0.20/0.41  cnf(c_0_117, negated_conjecture, (k2_zfmisc_1(esk6_0,esk7_0)=k2_zfmisc_1(esk2_0,esk3_0)|k2_zfmisc_1(X1,esk4_0)=k1_xboole_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_114])).
% 0.20/0.41  cnf(c_0_118, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk7_0,esk3_0)|v1_xboole_0(k2_zfmisc_1(X1,esk5_0))|v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_51, c_0_115])).
% 0.20/0.41  cnf(c_0_119, negated_conjecture, (k2_zfmisc_1(esk6_0,esk7_0)=k2_zfmisc_1(esk2_0,esk3_0)|esk5_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_43]), c_0_41])).
% 0.20/0.41  cnf(c_0_120, negated_conjecture, (k2_zfmisc_1(X1,esk5_0)=k1_xboole_0|esk6_0=k1_xboole_0|r1_tarski(esk7_0,esk3_0)|v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_118])).
% 0.20/0.41  cnf(c_0_121, negated_conjecture, (k1_relat_1(k2_zfmisc_1(esk2_0,esk3_0))=esk6_0|esk5_0=k1_xboole_0|v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_107, c_0_119])).
% 0.20/0.41  cnf(c_0_122, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk7_0,esk3_0)|v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_41, c_0_120])).
% 0.20/0.41  cnf(c_0_123, negated_conjecture, (esk5_0=k1_xboole_0|esk6_0=esk2_0|v1_xboole_0(esk7_0)|v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_107, c_0_121])).
% 0.20/0.41  cnf(c_0_124, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk7_0,esk3_0)|v1_xboole_0(k2_zfmisc_1(X1,esk4_0))), inference(spm,[status(thm)],[c_0_51, c_0_122])).
% 0.20/0.41  cnf(c_0_125, negated_conjecture, (esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0|esk5_0!=esk9_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_126, negated_conjecture, (esk6_0=esk2_0|esk5_0=k1_xboole_0|esk7_0=k1_xboole_0|v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_123])).
% 0.20/0.41  cnf(c_0_127, negated_conjecture, (k2_zfmisc_1(X1,esk4_0)=k1_xboole_0|esk6_0=k1_xboole_0|r1_tarski(esk7_0,esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_124])).
% 0.20/0.41  cnf(c_0_128, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(X1,esk7_0)|v1_xboole_0(X2)|~r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_26, c_0_119])).
% 0.20/0.41  cnf(c_0_129, negated_conjecture, (esk6_0!=esk2_0|esk7_0!=esk3_0|esk8_0!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_125, c_0_60])])).
% 0.20/0.41  cnf(c_0_130, negated_conjecture, (esk7_0=k1_xboole_0|esk5_0=k1_xboole_0|esk6_0=esk2_0|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_126])).
% 0.20/0.41  cnf(c_0_131, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk7_0,esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_127]), c_0_43]), c_0_41])).
% 0.20/0.41  cnf(c_0_132, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(esk3_0,esk7_0)|v1_xboole_0(esk2_0)), inference(spm,[status(thm)],[c_0_128, c_0_32])).
% 0.20/0.41  cnf(c_0_133, negated_conjecture, (esk6_0!=esk2_0|esk7_0!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129, c_0_106])])).
% 0.20/0.41  cnf(c_0_134, negated_conjecture, (esk3_0=k1_xboole_0|esk6_0=esk2_0|esk5_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_130]), c_0_62]), c_0_43]), c_0_43]), c_0_41])).
% 0.20/0.41  cnf(c_0_135, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0=esk3_0|~r1_tarski(esk3_0,esk7_0)), inference(spm,[status(thm)],[c_0_48, c_0_131])).
% 0.20/0.41  cnf(c_0_136, negated_conjecture, (esk5_0=k1_xboole_0|esk2_0=k1_xboole_0|r1_tarski(esk3_0,esk7_0)), inference(spm,[status(thm)],[c_0_24, c_0_132])).
% 0.20/0.41  cnf(c_0_137, negated_conjecture, (esk5_0=k1_xboole_0|esk3_0=k1_xboole_0|esk7_0!=esk3_0), inference(spm,[status(thm)],[c_0_133, c_0_134])).
% 0.20/0.41  cnf(c_0_138, negated_conjecture, (esk2_0=k1_xboole_0|esk5_0=k1_xboole_0|esk7_0=esk3_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_135, c_0_136])).
% 0.20/0.41  cnf(c_0_139, negated_conjecture, (esk6_0=k1_xboole_0|esk2_0=k1_xboole_0|esk3_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_137, c_0_138])).
% 0.20/0.41  cnf(c_0_140, negated_conjecture, (esk5_0=k1_xboole_0|esk3_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_139]), c_0_43]), c_0_43]), c_0_43]), c_0_41])).
% 0.20/0.41  cnf(c_0_141, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_140]), c_0_62])])).
% 0.20/0.41  cnf(c_0_142, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_141]), c_0_62]), c_0_43]), c_0_43])])).
% 0.20/0.41  cnf(c_0_143, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_142]), c_0_43]), c_0_43]), c_0_43])]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 144
% 0.20/0.41  # Proof object clause steps            : 119
% 0.20/0.41  # Proof object formula steps           : 25
% 0.20/0.41  # Proof object conjectures             : 89
% 0.20/0.41  # Proof object clause conjectures      : 86
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 16
% 0.20/0.41  # Proof object initial formulas used   : 12
% 0.20/0.41  # Proof object generating inferences   : 86
% 0.20/0.41  # Proof object simplifying inferences  : 74
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 12
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 17
% 0.20/0.41  # Removed in clause preprocessing      : 2
% 0.20/0.41  # Initial clauses in saturation        : 15
% 0.20/0.41  # Processed clauses                    : 381
% 0.20/0.41  # ...of these trivial                  : 4
% 0.20/0.41  # ...subsumed                          : 101
% 0.20/0.41  # ...remaining for further processing  : 276
% 0.20/0.41  # Other redundant clauses eliminated   : 4
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 111
% 0.20/0.41  # Backward-rewritten                   : 112
% 0.20/0.41  # Generated clauses                    : 2024
% 0.20/0.41  # ...of the previous two non-trivial   : 1597
% 0.20/0.41  # Contextual simplify-reflections      : 1
% 0.20/0.41  # Paramodulations                      : 2016
% 0.20/0.41  # Factorizations                       : 4
% 0.20/0.41  # Equation resolutions                 : 4
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 37
% 0.20/0.41  #    Positive orientable unit clauses  : 14
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 0
% 0.20/0.41  #    Non-unit-clauses                  : 23
% 0.20/0.41  # Current number of unprocessed clauses: 737
% 0.20/0.41  # ...number of literals in the above   : 3409
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 239
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 3794
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 1222
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 208
% 0.20/0.41  # Unit Clause-clause subsumption calls : 85
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 13
% 0.20/0.41  # BW rewrite match successes           : 12
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 28731
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.071 s
% 0.20/0.41  # System time              : 0.002 s
% 0.20/0.41  # Total time               : 0.073 s
% 0.20/0.41  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
