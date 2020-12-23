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
% DateTime   : Thu Dec  3 10:59:59 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 987 expanded)
%              Number of clauses        :   51 ( 448 expanded)
%              Number of leaves         :    9 ( 253 expanded)
%              Depth                    :   18
%              Number of atoms          :  168 (2039 expanded)
%              Number of equality atoms :  127 (1823 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :    9 (   2 average)
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

fof(t37_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
     => ( k3_zfmisc_1(X1,X2,X3) = k1_xboole_0
        | ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t134_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

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
    ! [X21,X22,X23,X24] : k4_zfmisc_1(X21,X22,X23,X24) = k2_zfmisc_1(k3_zfmisc_1(X21,X22,X23),X24) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X18,X19,X20] : k3_zfmisc_1(X18,X19,X20) = k2_zfmisc_1(k2_zfmisc_1(X18,X19),X20) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X28,X29,X30,X31,X32,X33] :
      ( ( X28 = X31
        | k3_zfmisc_1(X28,X29,X30) = k1_xboole_0
        | k3_zfmisc_1(X28,X29,X30) != k3_zfmisc_1(X31,X32,X33) )
      & ( X29 = X32
        | k3_zfmisc_1(X28,X29,X30) = k1_xboole_0
        | k3_zfmisc_1(X28,X29,X30) != k3_zfmisc_1(X31,X32,X33) )
      & ( X30 = X33
        | k3_zfmisc_1(X28,X29,X30) = k1_xboole_0
        | k3_zfmisc_1(X28,X29,X30) != k3_zfmisc_1(X31,X32,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_mcart_1])])])).

fof(c_0_13,negated_conjecture,
    ( k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0) = k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0)
    & k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0) != k1_xboole_0
    & ( esk2_0 != esk6_0
      | esk3_0 != esk7_0
      | esk4_0 != esk8_0
      | esk5_0 != esk9_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_14,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( X1 = X2
    | k3_zfmisc_1(X3,X4,X1) = k1_xboole_0
    | k3_zfmisc_1(X3,X4,X1) != k3_zfmisc_1(X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0) = k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( X1 = X2
    | k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1) != k2_zfmisc_1(k2_zfmisc_1(X5,X6),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_15]),c_0_15]),c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0),esk9_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( esk9_0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0) != k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_24,plain,
    ( X1 = X2
    | k3_zfmisc_1(X3,X1,X4) = k1_xboole_0
    | k3_zfmisc_1(X3,X1,X4) != k3_zfmisc_1(X5,X2,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( esk9_0 = esk5_0 ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_26,plain,
    ( X1 = X2
    | k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4) != k2_zfmisc_1(k2_zfmisc_1(X5,X2),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_15]),c_0_15]),c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0),esk5_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_21,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( esk8_0 = X1
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0) != k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_22])).

fof(c_0_29,plain,(
    ! [X25,X26,X27] :
      ( ( r2_hidden(k1_mcart_1(X25),X26)
        | ~ r2_hidden(X25,k2_zfmisc_1(X26,X27)) )
      & ( r2_hidden(k2_mcart_1(X25),X27)
        | ~ r2_hidden(X25,k2_zfmisc_1(X26,X27)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

fof(c_0_30,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_xboole_0(X9)
        | ~ r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_1(X11),X11)
        | v1_xboole_0(X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_31,plain,
    ( X1 = X2
    | k3_zfmisc_1(X1,X3,X4) = k1_xboole_0
    | k3_zfmisc_1(X1,X3,X4) != k3_zfmisc_1(X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( esk8_0 = esk4_0 ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( X1 = X2
    | k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4) = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4) != k2_zfmisc_1(k2_zfmisc_1(X2,X5),X6) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_15]),c_0_15]),c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk4_0),esk5_0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_32])).

fof(c_0_37,plain,(
    ! [X13] :
      ( ~ v1_xboole_0(X13)
      | X13 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_38,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( r2_hidden(k1_mcart_1(esk1_1(k2_zfmisc_1(X1,X2))),X1)
    | v1_xboole_0(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_40,plain,(
    ! [X14,X15,X16,X17] :
      ( ( X14 = X16
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0
        | k2_zfmisc_1(X14,X15) != k2_zfmisc_1(X16,X17) )
      & ( X15 = X17
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0
        | k2_zfmisc_1(X14,X15) != k2_zfmisc_1(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).

cnf(c_0_41,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) = k1_xboole_0
    | X1 = k2_zfmisc_1(esk6_0,esk7_0)
    | k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( esk2_0 != esk6_0
    | esk3_0 != esk7_0
    | esk4_0 != esk8_0
    | esk5_0 != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(X3,X1) != k2_zfmisc_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( k2_zfmisc_1(esk6_0,esk7_0) = k2_zfmisc_1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_41]),c_0_22])).

cnf(c_0_47,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_48,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_50,negated_conjecture,
    ( esk6_0 != esk2_0
    | esk7_0 != esk3_0
    | esk8_0 != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_25])])).

cnf(c_0_51,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = X1
    | k2_zfmisc_1(esk2_0,esk3_0) != k2_zfmisc_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_47])).

cnf(c_0_53,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_43])).

cnf(c_0_54,plain,
    ( r2_hidden(k2_mcart_1(esk1_1(k2_zfmisc_1(X1,X2))),X2)
    | v1_xboole_0(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_34])).

cnf(c_0_55,plain,
    ( X1 = X2
    | X1 = k1_xboole_0
    | X3 = k1_xboole_0
    | k2_zfmisc_1(X1,X3) != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_56,negated_conjecture,
    ( esk6_0 != esk2_0
    | esk7_0 != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_32])])).

cnf(c_0_57,negated_conjecture,
    ( esk7_0 = esk3_0
    | esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_53]),c_0_22])).

cnf(c_0_60,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk6_0 = X1
    | k2_zfmisc_1(esk2_0,esk3_0) != k2_zfmisc_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_46])).

cnf(c_0_62,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0
    | esk6_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_61]),c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_53]),c_0_63]),c_0_22])).

cnf(c_0_67,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_58])])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_58])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:58:47 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S0U
% 0.13/0.38  # and selection function SelectComplexExceptRRHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t57_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(k4_zfmisc_1(X1,X2,X3,X4)=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_mcart_1)).
% 0.13/0.38  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.13/0.38  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.13/0.38  fof(t37_mcart_1, axiom, ![X1, X2, X3, X4, X5, X6]:(k3_zfmisc_1(X1,X2,X3)=k3_zfmisc_1(X4,X5,X6)=>(k3_zfmisc_1(X1,X2,X3)=k1_xboole_0|((X1=X4&X2=X5)&X3=X6))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_mcart_1)).
% 0.13/0.38  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.13/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.13/0.38  fof(t134_zfmisc_1, axiom, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.13/0.38  fof(dt_o_0_0_xboole_0, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 0.13/0.38  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_zfmisc_1(X1,X2,X3,X4)=k4_zfmisc_1(X5,X6,X7,X8)=>(k4_zfmisc_1(X1,X2,X3,X4)=k1_xboole_0|(((X1=X5&X2=X6)&X3=X7)&X4=X8)))), inference(assume_negation,[status(cth)],[t57_mcart_1])).
% 0.13/0.38  fof(c_0_10, plain, ![X21, X22, X23, X24]:k4_zfmisc_1(X21,X22,X23,X24)=k2_zfmisc_1(k3_zfmisc_1(X21,X22,X23),X24), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.13/0.38  fof(c_0_11, plain, ![X18, X19, X20]:k3_zfmisc_1(X18,X19,X20)=k2_zfmisc_1(k2_zfmisc_1(X18,X19),X20), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.13/0.38  fof(c_0_12, plain, ![X28, X29, X30, X31, X32, X33]:(((X28=X31|k3_zfmisc_1(X28,X29,X30)=k1_xboole_0|k3_zfmisc_1(X28,X29,X30)!=k3_zfmisc_1(X31,X32,X33))&(X29=X32|k3_zfmisc_1(X28,X29,X30)=k1_xboole_0|k3_zfmisc_1(X28,X29,X30)!=k3_zfmisc_1(X31,X32,X33)))&(X30=X33|k3_zfmisc_1(X28,X29,X30)=k1_xboole_0|k3_zfmisc_1(X28,X29,X30)!=k3_zfmisc_1(X31,X32,X33))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_mcart_1])])])).
% 0.13/0.38  fof(c_0_13, negated_conjecture, (k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0)=k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0)&(k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0)!=k1_xboole_0&(esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0|esk5_0!=esk9_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.13/0.38  cnf(c_0_14, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_15, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_16, plain, (X1=X2|k3_zfmisc_1(X3,X4,X1)=k1_xboole_0|k3_zfmisc_1(X3,X4,X1)!=k3_zfmisc_1(X5,X6,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0)=k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_18, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_20, plain, (X1=X2|k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X3,X4),X1)!=k2_zfmisc_1(k2_zfmisc_1(X5,X6),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_15]), c_0_15]), c_0_15])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0),esk9_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_18])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_19, c_0_18])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (esk9_0=X1|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0)!=k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.13/0.38  cnf(c_0_24, plain, (X1=X2|k3_zfmisc_1(X3,X1,X4)=k1_xboole_0|k3_zfmisc_1(X3,X1,X4)!=k3_zfmisc_1(X5,X2,X6)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (esk9_0=esk5_0), inference(er,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_26, plain, (X1=X2|k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X3,X1),X4)!=k2_zfmisc_1(k2_zfmisc_1(X5,X2),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_15]), c_0_15]), c_0_15])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0),esk5_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0)), inference(rw,[status(thm)],[c_0_21, c_0_25])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (esk8_0=X1|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0)!=k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_22])).
% 0.13/0.38  fof(c_0_29, plain, ![X25, X26, X27]:((r2_hidden(k1_mcart_1(X25),X26)|~r2_hidden(X25,k2_zfmisc_1(X26,X27)))&(r2_hidden(k2_mcart_1(X25),X27)|~r2_hidden(X25,k2_zfmisc_1(X26,X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.13/0.38  fof(c_0_30, plain, ![X9, X10, X11]:((~v1_xboole_0(X9)|~r2_hidden(X10,X9))&(r2_hidden(esk1_1(X11),X11)|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.38  cnf(c_0_31, plain, (X1=X2|k3_zfmisc_1(X1,X3,X4)=k1_xboole_0|k3_zfmisc_1(X1,X3,X4)!=k3_zfmisc_1(X2,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (esk8_0=esk4_0), inference(er,[status(thm)],[c_0_28])).
% 0.13/0.38  cnf(c_0_33, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_34, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_35, plain, (X1=X2|k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4)=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X1,X3),X4)!=k2_zfmisc_1(k2_zfmisc_1(X2,X5),X6)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_15]), c_0_15]), c_0_15])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk4_0),esk5_0)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0)), inference(rw,[status(thm)],[c_0_27, c_0_32])).
% 0.13/0.38  fof(c_0_37, plain, ![X13]:(~v1_xboole_0(X13)|X13=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.13/0.38  cnf(c_0_38, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_39, plain, (r2_hidden(k1_mcart_1(esk1_1(k2_zfmisc_1(X1,X2))),X1)|v1_xboole_0(k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.38  fof(c_0_40, plain, ![X14, X15, X16, X17]:((X14=X16|(X14=k1_xboole_0|X15=k1_xboole_0)|k2_zfmisc_1(X14,X15)!=k2_zfmisc_1(X16,X17))&(X15=X17|(X14=k1_xboole_0|X15=k1_xboole_0)|k2_zfmisc_1(X14,X15)!=k2_zfmisc_1(X16,X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_zfmisc_1])])])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)=k1_xboole_0|X1=k2_zfmisc_1(esk6_0,esk7_0)|k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)!=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.38  cnf(c_0_42, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_43, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0|esk5_0!=esk9_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_45, plain, (X1=X2|X3=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(X3,X1)!=k2_zfmisc_1(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (k2_zfmisc_1(esk6_0,esk7_0)=k2_zfmisc_1(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_41]), c_0_22])).
% 0.13/0.38  cnf(c_0_47, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).
% 0.13/0.38  cnf(c_0_48, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.38  cnf(c_0_49, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (esk6_0!=esk2_0|esk7_0!=esk3_0|esk8_0!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_25])])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|esk7_0=X1|k2_zfmisc_1(esk2_0,esk3_0)!=k2_zfmisc_1(X2,X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.13/0.38  cnf(c_0_52, plain, (o_0_0_xboole_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_47])).
% 0.13/0.38  cnf(c_0_53, plain, (k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_48, c_0_43])).
% 0.13/0.38  cnf(c_0_54, plain, (r2_hidden(k2_mcart_1(esk1_1(k2_zfmisc_1(X1,X2))),X2)|v1_xboole_0(k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_49, c_0_34])).
% 0.13/0.38  cnf(c_0_55, plain, (X1=X2|X1=k1_xboole_0|X3=k1_xboole_0|k2_zfmisc_1(X1,X3)!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (esk6_0!=esk2_0|esk7_0!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_32])])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (esk7_0=esk3_0|esk6_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(er,[status(thm)],[c_0_51])).
% 0.13/0.38  cnf(c_0_58, plain, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_47, c_0_52])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(esk6_0,esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_53]), c_0_22])).
% 0.13/0.38  cnf(c_0_60, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_38, c_0_54])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0=k1_xboole_0|esk6_0=X1|k2_zfmisc_1(esk2_0,esk3_0)!=k2_zfmisc_1(X1,X2)), inference(spm,[status(thm)],[c_0_55, c_0_46])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0|esk6_0!=esk2_0), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.13/0.38  cnf(c_0_63, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_58])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_61]), c_0_62])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_53]), c_0_63]), c_0_22])).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_58])])).
% 0.13/0.38  cnf(c_0_68, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67]), c_0_58])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 69
% 0.13/0.38  # Proof object clause steps            : 51
% 0.13/0.38  # Proof object formula steps           : 18
% 0.13/0.38  # Proof object conjectures             : 28
% 0.13/0.38  # Proof object clause conjectures      : 25
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 16
% 0.13/0.38  # Proof object initial formulas used   : 9
% 0.13/0.38  # Proof object generating inferences   : 23
% 0.13/0.38  # Proof object simplifying inferences  : 32
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 9
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 16
% 0.13/0.38  # Removed in clause preprocessing      : 2
% 0.13/0.38  # Initial clauses in saturation        : 14
% 0.13/0.38  # Processed clauses                    : 368
% 0.13/0.38  # ...of these trivial                  : 3
% 0.13/0.38  # ...subsumed                          : 261
% 0.13/0.38  # ...remaining for further processing  : 104
% 0.13/0.38  # Other redundant clauses eliminated   : 52
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 10
% 0.13/0.38  # Backward-rewritten                   : 32
% 0.13/0.38  # Generated clauses                    : 1171
% 0.13/0.38  # ...of the previous two non-trivial   : 870
% 0.13/0.38  # Contextual simplify-reflections      : 1
% 0.13/0.38  # Paramodulations                      : 1099
% 0.13/0.38  # Factorizations                       : 2
% 0.13/0.38  # Equation resolutions                 : 70
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
% 0.13/0.38  # Current number of processed clauses  : 48
% 0.13/0.38  #    Positive orientable unit clauses  : 8
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 8
% 0.13/0.38  #    Non-unit-clauses                  : 32
% 0.13/0.38  # Current number of unprocessed clauses: 449
% 0.13/0.38  # ...number of literals in the above   : 1564
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 58
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 442
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 328
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 70
% 0.13/0.38  # Unit Clause-clause subsumption calls : 71
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 8
% 0.13/0.38  # BW rewrite match successes           : 7
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 12206
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.043 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.048 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
