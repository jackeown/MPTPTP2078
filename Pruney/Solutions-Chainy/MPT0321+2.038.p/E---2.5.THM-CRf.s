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
% DateTime   : Thu Dec  3 10:44:03 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 947 expanded)
%              Number of clauses        :   54 ( 454 expanded)
%              Number of leaves         :    8 ( 227 expanded)
%              Depth                    :   18
%              Number of atoms          :  172 (2821 expanded)
%              Number of equality atoms :   58 (1163 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t134_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_8,plain,(
    ! [X22,X23,X24] :
      ( ( r2_hidden(X22,X23)
        | ~ r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))) )
      & ( X22 != X24
        | ~ r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))) )
      & ( ~ r2_hidden(X22,X23)
        | X22 = X24
        | r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_9,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_10,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k2_tarski(X2,X2))) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_13,plain,(
    ! [X16] : k4_xboole_0(k1_xboole_0,X16) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X1,X1))) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X11,X12] :
      ( ( ~ r2_hidden(esk2_2(X11,X12),X11)
        | ~ r2_hidden(esk2_2(X11,X12),X12)
        | X11 = X12 )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r2_hidden(esk2_2(X11,X12),X12)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

fof(c_0_17,plain,(
    ! [X18,X19,X20,X21] :
      ( ( r2_hidden(X18,X20)
        | ~ r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,X21)) )
      & ( r2_hidden(X19,X21)
        | ~ r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,X21)) )
      & ( ~ r2_hidden(X18,X20)
        | ~ r2_hidden(X19,X21)
        | r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | ( X1 = X3
            & X2 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t134_zfmisc_1])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk2_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_23,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk5_0,esk6_0)
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & ( esk3_0 != esk5_0
      | esk4_0 != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_24,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_25,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(k4_tarski(X2,esk2_2(k1_xboole_0,X1)),k2_zfmisc_1(X3,X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(k4_tarski(X1,esk2_2(k1_xboole_0,esk6_0)),k2_zfmisc_1(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_2(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_34,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(k4_tarski(esk1_2(X2,X3),esk2_2(k1_xboole_0,X1)),k2_zfmisc_1(X2,X1))
    | r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(k4_tarski(esk1_2(esk5_0,X1),esk2_2(k1_xboole_0,esk6_0)),k2_zfmisc_1(esk3_0,esk4_0))
    | r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(X1,esk1_2(X2,X3)),k2_zfmisc_1(X4,X2))
    | r1_tarski(X2,X3)
    | ~ r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_21,c_0_28])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_2(X1,k1_xboole_0),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk2_2(k1_xboole_0,esk4_0),esk6_0)
    | r1_tarski(esk3_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_42,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_44,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk1_2(esk5_0,X1),esk3_0)
    | r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),esk5_0)
    | r1_tarski(esk3_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_34]),c_0_35])).

cnf(c_0_46,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(k4_tarski(esk2_2(k1_xboole_0,X1),esk1_2(X2,X3)),k2_zfmisc_1(X1,X2))
    | r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk2_2(k1_xboole_0,esk4_0),esk6_0)
    | r2_hidden(esk2_2(esk3_0,k1_xboole_0),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_48,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r1_tarski(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),esk6_0)
    | r1_tarski(esk4_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_46]),c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk2_2(k1_xboole_0,esk4_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])])).

cnf(c_0_54,plain,
    ( X1 = X2
    | r2_hidden(esk2_2(X1,X2),X2)
    | r2_hidden(esk2_2(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_19])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( esk3_0 != esk5_0
    | esk4_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_57,negated_conjecture,
    ( esk5_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_18])).

cnf(c_0_58,negated_conjecture,
    ( esk4_0 = X1
    | r2_hidden(esk2_2(esk4_0,X1),esk6_0)
    | r2_hidden(esk2_2(esk4_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( esk6_0 != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_2(k1_xboole_0,esk4_0)),k2_zfmisc_1(X2,esk6_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk2_2(esk3_0,k1_xboole_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_50]),c_0_41])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_58]),c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_2(esk3_0,k1_xboole_0),esk2_2(k1_xboole_0,esk4_0)),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_26])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_2(esk4_0,esk6_0)),k2_zfmisc_1(X2,esk6_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk2_2(esk3_0,k1_xboole_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk6_0) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_57])).

cnf(c_0_67,plain,
    ( X1 = X2
    | ~ r2_hidden(esk2_2(X1,X2),X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_2(esk3_0,k1_xboole_0),esk2_2(esk4_0,esk6_0)),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_hidden(esk2_2(esk4_0,esk6_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_62]),c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_68]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053N
% 0.19/0.47  # and selection function HSelectMinInfpos.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.027 s
% 0.19/0.47  # Presaturation interreduction done
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.19/0.47  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.47  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.19/0.47  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 0.19/0.47  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.19/0.47  fof(t134_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.19/0.47  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.47  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.47  fof(c_0_8, plain, ![X22, X23, X24]:(((r2_hidden(X22,X23)|~r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))))&(X22!=X24|~r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24)))))&(~r2_hidden(X22,X23)|X22=X24|r2_hidden(X22,k4_xboole_0(X23,k1_tarski(X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.19/0.47  fof(c_0_9, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.47  cnf(c_0_10, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.47  cnf(c_0_11, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.47  cnf(c_0_12, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k2_tarski(X2,X2)))), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.47  fof(c_0_13, plain, ![X16]:k4_xboole_0(k1_xboole_0,X16)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.19/0.47  cnf(c_0_14, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X1,X1)))), inference(er,[status(thm)],[c_0_12])).
% 0.19/0.47  cnf(c_0_15, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.47  fof(c_0_16, plain, ![X11, X12]:((~r2_hidden(esk2_2(X11,X12),X11)|~r2_hidden(esk2_2(X11,X12),X12)|X11=X12)&(r2_hidden(esk2_2(X11,X12),X11)|r2_hidden(esk2_2(X11,X12),X12)|X11=X12)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.19/0.47  fof(c_0_17, plain, ![X18, X19, X20, X21]:(((r2_hidden(X18,X20)|~r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,X21)))&(r2_hidden(X19,X21)|~r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,X21))))&(~r2_hidden(X18,X20)|~r2_hidden(X19,X21)|r2_hidden(k4_tarski(X18,X19),k2_zfmisc_1(X20,X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.19/0.47  cnf(c_0_18, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.47  cnf(c_0_19, plain, (r2_hidden(esk2_2(X1,X2),X1)|r2_hidden(esk2_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.47  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4)))), inference(assume_negation,[status(cth)],[t134_zfmisc_1])).
% 0.19/0.47  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.47  cnf(c_0_22, plain, (k1_xboole_0=X1|r2_hidden(esk2_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.47  fof(c_0_23, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk5_0,esk6_0)&((esk3_0!=k1_xboole_0&esk4_0!=k1_xboole_0)&(esk3_0!=esk5_0|esk4_0!=esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.19/0.47  fof(c_0_24, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.47  cnf(c_0_25, plain, (k1_xboole_0=X1|r2_hidden(k4_tarski(X2,esk2_2(k1_xboole_0,X1)),k2_zfmisc_1(X3,X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.47  cnf(c_0_26, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.47  cnf(c_0_27, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.47  cnf(c_0_28, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.47  cnf(c_0_29, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(k4_tarski(X1,esk2_2(k1_xboole_0,esk6_0)),k2_zfmisc_1(esk3_0,esk4_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.47  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.47  cnf(c_0_31, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.47  cnf(c_0_32, plain, (X1=k1_xboole_0|r2_hidden(esk2_2(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.47  cnf(c_0_33, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 0.19/0.47  cnf(c_0_34, plain, (k1_xboole_0=X1|r2_hidden(k4_tarski(esk1_2(X2,X3),esk2_2(k1_xboole_0,X1)),k2_zfmisc_1(X2,X1))|r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_25, c_0_28])).
% 0.19/0.47  cnf(c_0_35, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.47  cnf(c_0_36, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(k4_tarski(esk1_2(esk5_0,X1),esk2_2(k1_xboole_0,esk6_0)),k2_zfmisc_1(esk3_0,esk4_0))|r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 0.19/0.47  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_26])).
% 0.19/0.47  cnf(c_0_38, plain, (r2_hidden(k4_tarski(X1,esk1_2(X2,X3)),k2_zfmisc_1(X4,X2))|r1_tarski(X2,X3)|~r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_21, c_0_28])).
% 0.19/0.47  cnf(c_0_39, plain, (X1=k1_xboole_0|r2_hidden(esk2_2(X1,k1_xboole_0),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.47  cnf(c_0_40, negated_conjecture, (r2_hidden(esk2_2(k1_xboole_0,esk4_0),esk6_0)|r1_tarski(esk3_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.19/0.47  cnf(c_0_41, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.47  fof(c_0_42, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.47  cnf(c_0_43, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.47  cnf(c_0_44, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk1_2(esk5_0,X1),esk3_0)|r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_30, c_0_36])).
% 0.19/0.47  cnf(c_0_45, negated_conjecture, (r2_hidden(esk1_2(esk3_0,X1),esk5_0)|r1_tarski(esk3_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_34]), c_0_35])).
% 0.19/0.47  cnf(c_0_46, plain, (k1_xboole_0=X1|r2_hidden(k4_tarski(esk2_2(k1_xboole_0,X1),esk1_2(X2,X3)),k2_zfmisc_1(X1,X2))|r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_38, c_0_22])).
% 0.19/0.47  cnf(c_0_47, negated_conjecture, (r2_hidden(esk2_2(k1_xboole_0,esk4_0),esk6_0)|r2_hidden(esk2_2(esk3_0,k1_xboole_0),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.19/0.47  cnf(c_0_48, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.47  cnf(c_0_49, negated_conjecture, (esk6_0=k1_xboole_0|r1_tarski(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.47  cnf(c_0_50, negated_conjecture, (r1_tarski(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_43, c_0_45])).
% 0.19/0.47  cnf(c_0_51, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),esk6_0)|r1_tarski(esk4_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_46]), c_0_41])).
% 0.19/0.47  cnf(c_0_52, negated_conjecture, (r2_hidden(esk2_2(k1_xboole_0,esk4_0),esk6_0)), inference(spm,[status(thm)],[c_0_14, c_0_47])).
% 0.19/0.47  cnf(c_0_53, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])])).
% 0.19/0.47  cnf(c_0_54, plain, (X1=X2|r2_hidden(esk2_2(X1,X2),X2)|r2_hidden(esk2_2(X1,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_31, c_0_19])).
% 0.19/0.47  cnf(c_0_55, negated_conjecture, (r1_tarski(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_43, c_0_51])).
% 0.19/0.47  cnf(c_0_56, negated_conjecture, (esk3_0!=esk5_0|esk4_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.47  cnf(c_0_57, negated_conjecture, (esk5_0=esk3_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_18])).
% 0.19/0.47  cnf(c_0_58, negated_conjecture, (esk4_0=X1|r2_hidden(esk2_2(esk4_0,X1),esk6_0)|r2_hidden(esk2_2(esk4_0,X1),X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.47  cnf(c_0_59, negated_conjecture, (esk6_0!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])])).
% 0.19/0.47  cnf(c_0_60, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_2(k1_xboole_0,esk4_0)),k2_zfmisc_1(X2,esk6_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_52])).
% 0.19/0.47  cnf(c_0_61, negated_conjecture, (r2_hidden(esk2_2(esk3_0,k1_xboole_0),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_50]), c_0_41])).
% 0.19/0.47  cnf(c_0_62, negated_conjecture, (r2_hidden(esk2_2(esk4_0,esk6_0),esk6_0)), inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_58]), c_0_59])).
% 0.19/0.47  cnf(c_0_63, negated_conjecture, (r2_hidden(k4_tarski(esk2_2(esk3_0,k1_xboole_0),esk2_2(k1_xboole_0,esk4_0)),k2_zfmisc_1(esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_26])).
% 0.19/0.47  cnf(c_0_64, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_2(esk4_0,esk6_0)),k2_zfmisc_1(X2,esk6_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_62])).
% 0.19/0.47  cnf(c_0_65, negated_conjecture, (r2_hidden(esk2_2(esk3_0,k1_xboole_0),esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_63])).
% 0.19/0.47  cnf(c_0_66, negated_conjecture, (k2_zfmisc_1(esk3_0,esk6_0)=k2_zfmisc_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_26, c_0_57])).
% 0.19/0.47  cnf(c_0_67, plain, (X1=X2|~r2_hidden(esk2_2(X1,X2),X1)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.47  cnf(c_0_68, negated_conjecture, (r2_hidden(k4_tarski(esk2_2(esk3_0,k1_xboole_0),esk2_2(esk4_0,esk6_0)),k2_zfmisc_1(esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])).
% 0.19/0.47  cnf(c_0_69, negated_conjecture, (~r2_hidden(esk2_2(esk4_0,esk6_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_62]), c_0_59])).
% 0.19/0.47  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_68]), c_0_69]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 71
% 0.19/0.47  # Proof object clause steps            : 54
% 0.19/0.47  # Proof object formula steps           : 17
% 0.19/0.47  # Proof object conjectures             : 34
% 0.19/0.47  # Proof object clause conjectures      : 31
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 16
% 0.19/0.47  # Proof object initial formulas used   : 8
% 0.19/0.47  # Proof object generating inferences   : 34
% 0.19/0.47  # Proof object simplifying inferences  : 18
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 8
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 20
% 0.19/0.47  # Removed in clause preprocessing      : 1
% 0.19/0.47  # Initial clauses in saturation        : 19
% 0.19/0.47  # Processed clauses                    : 650
% 0.19/0.47  # ...of these trivial                  : 6
% 0.19/0.47  # ...subsumed                          : 252
% 0.19/0.47  # ...remaining for further processing  : 392
% 0.19/0.47  # Other redundant clauses eliminated   : 3
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 18
% 0.19/0.47  # Backward-rewritten                   : 103
% 0.19/0.47  # Generated clauses                    : 6724
% 0.19/0.47  # ...of the previous two non-trivial   : 6424
% 0.19/0.47  # Contextual simplify-reflections      : 0
% 0.19/0.47  # Paramodulations                      : 6699
% 0.19/0.47  # Factorizations                       : 22
% 0.19/0.47  # Equation resolutions                 : 3
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 250
% 0.19/0.47  #    Positive orientable unit clauses  : 79
% 0.19/0.47  #    Positive unorientable unit clauses: 0
% 0.19/0.47  #    Negative unit clauses             : 7
% 0.19/0.47  #    Non-unit-clauses                  : 164
% 0.19/0.47  # Current number of unprocessed clauses: 5398
% 0.19/0.47  # ...number of literals in the above   : 15827
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 140
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 8461
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 5290
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 260
% 0.19/0.47  # Unit Clause-clause subsumption calls : 3234
% 0.19/0.47  # Rewrite failures with RHS unbound    : 0
% 0.19/0.47  # BW rewrite match attempts            : 333
% 0.19/0.47  # BW rewrite match successes           : 6
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 126745
% 0.19/0.48  
% 0.19/0.48  # -------------------------------------------------
% 0.19/0.48  # User time                : 0.133 s
% 0.19/0.48  # System time              : 0.006 s
% 0.19/0.48  # Total time               : 0.139 s
% 0.19/0.48  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
