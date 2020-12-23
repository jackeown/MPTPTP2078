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
% DateTime   : Thu Dec  3 10:44:09 EST 2020

% Result     : Theorem 20.99s
% Output     : CNFRefutation 20.99s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 598 expanded)
%              Number of clauses        :   56 ( 283 expanded)
%              Number of leaves         :   11 ( 151 expanded)
%              Depth                    :   16
%              Number of atoms          :  199 (1519 expanded)
%              Number of equality atoms :   77 ( 616 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t138_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t117_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_11,plain,(
    ! [X20,X21] :
      ( ( r1_tarski(X20,X21)
        | X20 != X21 )
      & ( r1_tarski(X21,X20)
        | X20 != X21 )
      & ( ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X21,X20)
        | X20 = X21 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_12,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | k3_xboole_0(X24,X25) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_13,plain,(
    ! [X26,X27] : k4_xboole_0(X26,k4_xboole_0(X26,X27)) = k3_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_14,plain,(
    ! [X22,X23] :
      ( ( k4_xboole_0(X22,X23) != k1_xboole_0
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(X22,X23)
        | k4_xboole_0(X22,X23) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X36,X37,X38,X39] : k2_zfmisc_1(k3_xboole_0(X36,X37),k3_xboole_0(X38,X39)) = k3_xboole_0(k2_zfmisc_1(X36,X38),k2_zfmisc_1(X37,X39)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_15])).

fof(c_0_22,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))
    & k2_zfmisc_1(esk3_0,esk4_0) != k1_xboole_0
    & ( ~ r1_tarski(esk3_0,esk5_0)
      | ~ r1_tarski(esk4_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_23,plain,(
    ! [X30,X31,X32] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X31,X30),k2_zfmisc_1(X32,X30))
        | X30 = k1_xboole_0
        | r1_tarski(X31,X32) )
      & ( ~ r1_tarski(k2_zfmisc_1(X30,X31),k2_zfmisc_1(X30,X32))
        | X30 = k1_xboole_0
        | r1_tarski(X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).

cnf(c_0_24,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_27,plain,(
    ! [X28,X29] :
      ( ( k2_zfmisc_1(X28,X29) != k1_xboole_0
        | X28 = k1_xboole_0
        | X29 = k1_xboole_0 )
      & ( X28 != k1_xboole_0
        | k2_zfmisc_1(X28,X29) = k1_xboole_0 )
      & ( X29 != k1_xboole_0
        | k2_zfmisc_1(X28,X29) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_30,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_19]),c_0_19]),c_0_19])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_21]),c_0_26])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_28])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | r1_tarski(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5)))
    | ~ r1_tarski(k2_zfmisc_1(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k2_zfmisc_1(X4,X1),k4_xboole_0(k2_zfmisc_1(X4,X1),k2_zfmisc_1(X5,X2)))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_26]),c_0_32])).

cnf(c_0_38,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) = k1_xboole_0
    | k4_xboole_0(X2,k4_xboole_0(X2,X4)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k1_xboole_0) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_28]),c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_41,plain,(
    ! [X33,X34,X35] :
      ( ( r1_tarski(k2_zfmisc_1(X33,X35),k2_zfmisc_1(X34,X35))
        | ~ r1_tarski(X33,X34) )
      & ( r1_tarski(k2_zfmisc_1(X35,X33),k2_zfmisc_1(X35,X34))
        | ~ r1_tarski(X33,X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X2,k4_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_35,c_0_19])).

fof(c_0_43,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | r1_tarski(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5)))
    | ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(X3,X1),k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))),k4_xboole_0(k2_zfmisc_1(X4,X1),k4_xboole_0(k2_zfmisc_1(X4,X1),k2_zfmisc_1(X5,X2)))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_34]),c_0_39]),c_0_40])).

cnf(c_0_47,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X4,k4_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_44,c_0_19])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)))
    | ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(X1,esk4_0),k4_xboole_0(k2_zfmisc_1(X1,esk4_0),k2_zfmisc_1(X1,esk6_0))),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_34]),c_0_32]),c_0_46])).

cnf(c_0_52,plain,
    ( r1_tarski(k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))),k2_zfmisc_1(X1,X4))
    | ~ r1_tarski(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X4) ),
    inference(spm,[status(thm)],[c_0_47,c_0_37])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),X1)
    | r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)))
    | ~ r1_tarski(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | r1_tarski(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5)))
    | ~ r1_tarski(k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),k4_xboole_0(k2_zfmisc_1(X1,X4),k4_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X2,X5)))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_31])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_56])).

cnf(c_0_62,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_63,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),X2)
    | r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_49])).

cnf(c_0_64,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,k4_xboole_0(X3,k4_xboole_0(X3,X4)))
    | k4_xboole_0(X1,X5) != k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X5,X4)))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_62])).

cnf(c_0_68,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_59])])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))
    | k4_xboole_0(esk3_0,esk5_0) != k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,X1),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_34]),c_0_32]),c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))
    | k4_xboole_0(esk3_0,esk5_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_21])).

cnf(c_0_73,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73])])).

cnf(c_0_75,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk5_0)
    | ~ r1_tarski(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_76,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_74]),c_0_59])])).

cnf(c_0_77,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_71])])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_76]),c_0_77]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:48:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 20.99/21.18  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 20.99/21.18  # and selection function SelectMaxLComplexAvoidPosPred.
% 20.99/21.18  #
% 20.99/21.18  # Preprocessing time       : 0.028 s
% 20.99/21.18  # Presaturation interreduction done
% 20.99/21.18  
% 20.99/21.18  # Proof found!
% 20.99/21.18  # SZS status Theorem
% 20.99/21.18  # SZS output start CNFRefutation
% 20.99/21.18  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 20.99/21.18  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 20.99/21.18  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 20.99/21.18  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 20.99/21.18  fof(t138_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 20.99/21.18  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 20.99/21.18  fof(t117_zfmisc_1, axiom, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 20.99/21.18  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 20.99/21.18  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 20.99/21.18  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 20.99/21.18  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 20.99/21.18  fof(c_0_11, plain, ![X20, X21]:(((r1_tarski(X20,X21)|X20!=X21)&(r1_tarski(X21,X20)|X20!=X21))&(~r1_tarski(X20,X21)|~r1_tarski(X21,X20)|X20=X21)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 20.99/21.18  fof(c_0_12, plain, ![X24, X25]:(~r1_tarski(X24,X25)|k3_xboole_0(X24,X25)=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 20.99/21.18  fof(c_0_13, plain, ![X26, X27]:k4_xboole_0(X26,k4_xboole_0(X26,X27))=k3_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 20.99/21.18  fof(c_0_14, plain, ![X22, X23]:((k4_xboole_0(X22,X23)!=k1_xboole_0|r1_tarski(X22,X23))&(~r1_tarski(X22,X23)|k4_xboole_0(X22,X23)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 20.99/21.18  cnf(c_0_15, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 20.99/21.18  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4))))), inference(assume_negation,[status(cth)],[t138_zfmisc_1])).
% 20.99/21.18  fof(c_0_17, plain, ![X36, X37, X38, X39]:k2_zfmisc_1(k3_xboole_0(X36,X37),k3_xboole_0(X38,X39))=k3_xboole_0(k2_zfmisc_1(X36,X38),k2_zfmisc_1(X37,X39)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 20.99/21.18  cnf(c_0_18, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 20.99/21.18  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 20.99/21.18  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 20.99/21.18  cnf(c_0_21, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_15])).
% 20.99/21.18  fof(c_0_22, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))&(k2_zfmisc_1(esk3_0,esk4_0)!=k1_xboole_0&(~r1_tarski(esk3_0,esk5_0)|~r1_tarski(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 20.99/21.18  fof(c_0_23, plain, ![X30, X31, X32]:((~r1_tarski(k2_zfmisc_1(X31,X30),k2_zfmisc_1(X32,X30))|X30=k1_xboole_0|r1_tarski(X31,X32))&(~r1_tarski(k2_zfmisc_1(X30,X31),k2_zfmisc_1(X30,X32))|X30=k1_xboole_0|r1_tarski(X31,X32))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).
% 20.99/21.18  cnf(c_0_24, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 20.99/21.18  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 20.99/21.18  cnf(c_0_26, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 20.99/21.18  fof(c_0_27, plain, ![X28, X29]:((k2_zfmisc_1(X28,X29)!=k1_xboole_0|(X28=k1_xboole_0|X29=k1_xboole_0))&((X28!=k1_xboole_0|k2_zfmisc_1(X28,X29)=k1_xboole_0)&(X29!=k1_xboole_0|k2_zfmisc_1(X28,X29)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 20.99/21.18  cnf(c_0_28, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 20.99/21.18  fof(c_0_29, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 20.99/21.18  cnf(c_0_30, plain, (X2=k1_xboole_0|r1_tarski(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 20.99/21.18  cnf(c_0_31, plain, (k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4)))=k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_19]), c_0_19]), c_0_19])).
% 20.99/21.18  cnf(c_0_32, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_21]), c_0_26])).
% 20.99/21.18  cnf(c_0_33, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 20.99/21.18  cnf(c_0_34, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,esk6_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_28])).
% 20.99/21.18  cnf(c_0_35, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 20.99/21.18  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|r1_tarski(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5)))|~r1_tarski(k2_zfmisc_1(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k2_zfmisc_1(X4,X1),k4_xboole_0(k2_zfmisc_1(X4,X1),k2_zfmisc_1(X5,X2))))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 20.99/21.18  cnf(c_0_37, plain, (k2_zfmisc_1(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_26]), c_0_32])).
% 20.99/21.18  cnf(c_0_38, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))=k1_xboole_0|k4_xboole_0(X2,k4_xboole_0(X2,X4))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_31])).
% 20.99/21.18  cnf(c_0_39, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k1_xboole_0)=k2_zfmisc_1(esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_28]), c_0_34])).
% 20.99/21.18  cnf(c_0_40, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 20.99/21.18  fof(c_0_41, plain, ![X33, X34, X35]:((r1_tarski(k2_zfmisc_1(X33,X35),k2_zfmisc_1(X34,X35))|~r1_tarski(X33,X34))&(r1_tarski(k2_zfmisc_1(X35,X33),k2_zfmisc_1(X35,X34))|~r1_tarski(X33,X34))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 20.99/21.18  cnf(c_0_42, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X2,k4_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_35, c_0_19])).
% 20.99/21.18  fof(c_0_43, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 20.99/21.18  cnf(c_0_44, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 20.99/21.18  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|r1_tarski(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5)))|~r1_tarski(k4_xboole_0(k2_zfmisc_1(X3,X1),k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))),k4_xboole_0(k2_zfmisc_1(X4,X1),k4_xboole_0(k2_zfmisc_1(X4,X1),k2_zfmisc_1(X5,X2))))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 20.99/21.18  cnf(c_0_46, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))!=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_34]), c_0_39]), c_0_40])).
% 20.99/21.18  cnf(c_0_47, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 20.99/21.18  cnf(c_0_48, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_42])).
% 20.99/21.18  cnf(c_0_49, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 20.99/21.18  cnf(c_0_50, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X4,k4_xboole_0(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_44, c_0_19])).
% 20.99/21.18  cnf(c_0_51, negated_conjecture, (r1_tarski(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)))|~r1_tarski(k4_xboole_0(k2_zfmisc_1(X1,esk4_0),k4_xboole_0(k2_zfmisc_1(X1,esk4_0),k2_zfmisc_1(X1,esk6_0))),k2_zfmisc_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_34]), c_0_32]), c_0_46])).
% 20.99/21.18  cnf(c_0_52, plain, (r1_tarski(k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))),k2_zfmisc_1(X1,X4))|~r1_tarski(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X4)), inference(spm,[status(thm)],[c_0_47, c_0_37])).
% 20.99/21.18  cnf(c_0_53, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 20.99/21.18  cnf(c_0_54, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),X1)|r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 20.99/21.18  cnf(c_0_55, plain, (X1=k1_xboole_0|r1_tarski(X2,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 20.99/21.18  cnf(c_0_56, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 20.99/21.18  cnf(c_0_57, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(er,[status(thm)],[c_0_50])).
% 20.99/21.18  cnf(c_0_58, negated_conjecture, (r1_tarski(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)))|~r1_tarski(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)),esk4_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 20.99/21.18  cnf(c_0_59, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 20.99/21.18  cnf(c_0_60, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|r1_tarski(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5)))|~r1_tarski(k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),k4_xboole_0(k2_zfmisc_1(X1,X4),k4_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X2,X5))))), inference(spm,[status(thm)],[c_0_55, c_0_31])).
% 20.99/21.18  cnf(c_0_61, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_56])).
% 20.99/21.18  cnf(c_0_62, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 20.99/21.18  cnf(c_0_63, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),X2)|r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_57, c_0_49])).
% 20.99/21.18  cnf(c_0_64, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 20.99/21.18  cnf(c_0_65, negated_conjecture, (r1_tarski(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59])])).
% 20.99/21.18  cnf(c_0_66, plain, (X1=k1_xboole_0|r1_tarski(X2,k4_xboole_0(X3,k4_xboole_0(X3,X4)))|k4_xboole_0(X1,X5)!=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X5,X4))))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 20.99/21.18  cnf(c_0_67, negated_conjecture, (esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_62])).
% 20.99/21.18  cnf(c_0_68, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_53, c_0_63])).
% 20.99/21.18  cnf(c_0_69, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_59])])).
% 20.99/21.18  cnf(c_0_70, negated_conjecture, (r1_tarski(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))|k4_xboole_0(esk3_0,esk5_0)!=k1_xboole_0|~r1_tarski(k2_zfmisc_1(esk3_0,X1),k2_zfmisc_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_34]), c_0_32]), c_0_67])).
% 20.99/21.18  cnf(c_0_71, negated_conjecture, (r1_tarski(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 20.99/21.18  cnf(c_0_72, negated_conjecture, (r1_tarski(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))|k4_xboole_0(esk3_0,esk5_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_21])).
% 20.99/21.18  cnf(c_0_73, negated_conjecture, (k4_xboole_0(esk3_0,esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_71])).
% 20.99/21.18  cnf(c_0_74, negated_conjecture, (r1_tarski(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73])])).
% 20.99/21.18  cnf(c_0_75, negated_conjecture, (~r1_tarski(esk3_0,esk5_0)|~r1_tarski(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 20.99/21.18  cnf(c_0_76, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_74]), c_0_59])])).
% 20.99/21.18  cnf(c_0_77, negated_conjecture, (~r1_tarski(esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_71])])).
% 20.99/21.18  cnf(c_0_78, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_76]), c_0_77]), ['proof']).
% 20.99/21.18  # SZS output end CNFRefutation
% 20.99/21.18  # Proof object total steps             : 79
% 20.99/21.18  # Proof object clause steps            : 56
% 20.99/21.18  # Proof object formula steps           : 23
% 20.99/21.18  # Proof object conjectures             : 22
% 20.99/21.18  # Proof object clause conjectures      : 19
% 20.99/21.18  # Proof object formula conjectures     : 3
% 20.99/21.18  # Proof object initial clauses used    : 19
% 20.99/21.18  # Proof object initial formulas used   : 11
% 20.99/21.18  # Proof object generating inferences   : 28
% 20.99/21.18  # Proof object simplifying inferences  : 28
% 20.99/21.18  # Training examples: 0 positive, 0 negative
% 20.99/21.18  # Parsed axioms                        : 11
% 20.99/21.18  # Removed by relevancy pruning/SinE    : 0
% 20.99/21.18  # Initial clauses                      : 27
% 20.99/21.18  # Removed in clause preprocessing      : 1
% 20.99/21.18  # Initial clauses in saturation        : 26
% 20.99/21.18  # Processed clauses                    : 82908
% 20.99/21.18  # ...of these trivial                  : 2419
% 20.99/21.18  # ...subsumed                          : 75414
% 20.99/21.18  # ...remaining for further processing  : 5075
% 20.99/21.18  # Other redundant clauses eliminated   : 64
% 20.99/21.18  # Clauses deleted for lack of memory   : 0
% 20.99/21.18  # Backward-subsumed                    : 528
% 20.99/21.18  # Backward-rewritten                   : 258
% 20.99/21.18  # Generated clauses                    : 1892799
% 20.99/21.18  # ...of the previous two non-trivial   : 1694937
% 20.99/21.18  # Contextual simplify-reflections      : 177
% 20.99/21.18  # Paramodulations                      : 1892538
% 20.99/21.18  # Factorizations                       : 28
% 20.99/21.18  # Equation resolutions                 : 233
% 20.99/21.18  # Propositional unsat checks           : 0
% 20.99/21.18  #    Propositional check models        : 0
% 20.99/21.18  #    Propositional check unsatisfiable : 0
% 20.99/21.18  #    Propositional clauses             : 0
% 20.99/21.18  #    Propositional clauses after purity: 0
% 20.99/21.18  #    Propositional unsat core size     : 0
% 20.99/21.18  #    Propositional preprocessing time  : 0.000
% 20.99/21.18  #    Propositional encoding time       : 0.000
% 20.99/21.18  #    Propositional solver time         : 0.000
% 20.99/21.18  #    Success case prop preproc time    : 0.000
% 20.99/21.18  #    Success case prop encoding time   : 0.000
% 20.99/21.18  #    Success case prop solver time     : 0.000
% 20.99/21.18  # Current number of processed clauses  : 4262
% 20.99/21.18  #    Positive orientable unit clauses  : 33
% 20.99/21.18  #    Positive unorientable unit clauses: 5
% 20.99/21.18  #    Negative unit clauses             : 23
% 20.99/21.18  #    Non-unit-clauses                  : 4201
% 20.99/21.18  # Current number of unprocessed clauses: 1586702
% 20.99/21.18  # ...number of literals in the above   : 8282001
% 20.99/21.18  # Current number of archived formulas  : 0
% 20.99/21.18  # Current number of archived clauses   : 812
% 20.99/21.18  # Clause-clause subsumption calls (NU) : 3148482
% 20.99/21.18  # Rec. Clause-clause subsumption calls : 1052247
% 20.99/21.18  # Non-unit clause-clause subsumptions  : 27066
% 20.99/21.18  # Unit Clause-clause subsumption calls : 20786
% 20.99/21.18  # Rewrite failures with RHS unbound    : 0
% 20.99/21.18  # BW rewrite match attempts            : 1394
% 20.99/21.18  # BW rewrite match successes           : 119
% 20.99/21.18  # Condensation attempts                : 0
% 20.99/21.18  # Condensation successes               : 0
% 20.99/21.18  # Termbank termtop insertions          : 61819754
% 21.05/21.24  
% 21.05/21.24  # -------------------------------------------------
% 21.05/21.24  # User time                : 20.237 s
% 21.05/21.24  # System time              : 0.671 s
% 21.05/21.24  # Total time               : 20.908 s
% 21.05/21.24  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
