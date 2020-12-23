%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:08 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 167 expanded)
%              Number of clauses        :   34 (  72 expanded)
%              Number of leaves         :   12 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  161 ( 372 expanded)
%              Number of equality atoms :   47 ( 149 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t15_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))
     => ( ( k1_mcart_1(X1) = X2
          | k1_mcart_1(X1) = X3 )
        & r2_hidden(k2_mcart_1(X1),X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t72_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t12_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))
     => ( k1_mcart_1(X1) = X2
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))
       => ( ( k1_mcart_1(X1) = X2
            | k1_mcart_1(X1) = X3 )
          & r2_hidden(k2_mcart_1(X1),X4) ) ) ),
    inference(assume_negation,[status(cth)],[t15_mcart_1])).

fof(c_0_13,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_14,plain,(
    ! [X29,X30,X31] :
      ( ( ~ r2_hidden(X29,X31)
        | k4_xboole_0(k2_tarski(X29,X30),X31) != k2_tarski(X29,X30) )
      & ( ~ r2_hidden(X30,X31)
        | k4_xboole_0(k2_tarski(X29,X30),X31) != k2_tarski(X29,X30) )
      & ( r2_hidden(X29,X31)
        | r2_hidden(X30,X31)
        | k4_xboole_0(k2_tarski(X29,X30),X31) = k2_tarski(X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).

fof(c_0_15,plain,(
    ! [X17,X18] : k1_enumset1(X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X19,X20,X21] : k2_enumset1(X19,X19,X20,X21) = k1_enumset1(X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),esk5_0))
    & ( k1_mcart_1(esk2_0) != esk3_0
      | ~ r2_hidden(k2_mcart_1(esk2_0),esk5_0) )
    & ( k1_mcart_1(esk2_0) != esk4_0
      | ~ r2_hidden(k2_mcart_1(esk2_0),esk5_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | k4_xboole_0(k2_tarski(X1,X3),X2) = k2_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X32,X33,X34] :
      ( ( r2_hidden(k1_mcart_1(X32),X33)
        | ~ r2_hidden(X32,k2_zfmisc_1(X33,X34)) )
      & ( r2_hidden(k2_mcart_1(X32),X34)
        | ~ r2_hidden(X32,k2_zfmisc_1(X33,X34)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X26,X27,X28] :
      ( ( r2_hidden(X26,X28)
        | ~ r1_tarski(k2_tarski(X26,X27),X28) )
      & ( r2_hidden(X27,X28)
        | ~ r1_tarski(k2_tarski(X26,X27),X28) )
      & ( ~ r2_hidden(X26,X28)
        | ~ r2_hidden(X27,X28)
        | r1_tarski(k2_tarski(X26,X27),X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_25,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X3),X2) = k2_enumset1(X1,X1,X1,X3)
    | r2_hidden(X3,X2)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_20]),c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X22,X23,X24,X25] :
      ( ( r2_hidden(X22,X24)
        | ~ r2_hidden(k4_tarski(X22,X23),k2_zfmisc_1(X24,X25)) )
      & ( r2_hidden(X23,X25)
        | ~ r2_hidden(k4_tarski(X22,X23),k2_zfmisc_1(X24,X25)) )
      & ( ~ r2_hidden(X22,X24)
        | ~ r2_hidden(X23,X25)
        | r2_hidden(k4_tarski(X22,X23),k2_zfmisc_1(X24,X25)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_33,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X4,k2_enumset1(X1,X1,X1,X3))
    | ~ r2_hidden(X4,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_enumset1(X1,X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_20]),c_0_21])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_31])).

fof(c_0_38,plain,(
    ! [X35,X36,X37] :
      ( ( k1_mcart_1(X35) = X36
        | ~ r2_hidden(X35,k2_zfmisc_1(k1_tarski(X36),X37)) )
      & ( r2_hidden(k2_mcart_1(X35),X37)
        | ~ r2_hidden(X35,k2_zfmisc_1(k1_tarski(X36),X37)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_mcart_1])])])).

fof(c_0_39,plain,(
    ! [X16] : k2_tarski(X16,X16) = k1_tarski(X16) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk4_0,X1)
    | r2_hidden(esk3_0,X1)
    | ~ r2_hidden(k1_mcart_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k2_mcart_1(esk2_0)),k2_zfmisc_1(X2,esk5_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1))
    | r2_hidden(esk4_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_48,plain,(
    ! [X38,X39] :
      ( k1_mcart_1(k4_tarski(X38,X39)) = X38
      & k2_mcart_1(k4_tarski(X38,X39)) = X39 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_49,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk4_0
    | ~ r2_hidden(k2_mcart_1(esk2_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_50,plain,
    ( k1_mcart_1(X1) = X2
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_20]),c_0_21])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,k2_mcart_1(esk2_0)),k2_zfmisc_1(k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1),esk5_0))
    | r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_41])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_55,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk3_0
    | ~ r2_hidden(k2_mcart_1(esk2_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,k2_mcart_1(esk2_0)),k2_zfmisc_1(k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0)),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_41])])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_56]),c_0_52]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:02:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.39/0.63  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.39/0.63  # and selection function SelectNegativeLiterals.
% 0.39/0.63  #
% 0.39/0.63  # Preprocessing time       : 0.040 s
% 0.39/0.63  # Presaturation interreduction done
% 0.39/0.63  
% 0.39/0.63  # Proof found!
% 0.39/0.63  # SZS status Theorem
% 0.39/0.63  # SZS output start CNFRefutation
% 0.39/0.63  fof(t15_mcart_1, conjecture, ![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&r2_hidden(k2_mcart_1(X1),X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_mcart_1)).
% 0.39/0.63  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.39/0.63  fof(t72_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 0.39/0.63  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.39/0.63  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.39/0.63  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.39/0.63  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.39/0.63  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.39/0.63  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.39/0.63  fof(t12_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))=>(k1_mcart_1(X1)=X2&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 0.39/0.63  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.39/0.63  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.39/0.63  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4]:(r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))=>((k1_mcart_1(X1)=X2|k1_mcart_1(X1)=X3)&r2_hidden(k2_mcart_1(X1),X4)))), inference(assume_negation,[status(cth)],[t15_mcart_1])).
% 0.39/0.63  fof(c_0_13, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.39/0.63  fof(c_0_14, plain, ![X29, X30, X31]:(((~r2_hidden(X29,X31)|k4_xboole_0(k2_tarski(X29,X30),X31)!=k2_tarski(X29,X30))&(~r2_hidden(X30,X31)|k4_xboole_0(k2_tarski(X29,X30),X31)!=k2_tarski(X29,X30)))&(r2_hidden(X29,X31)|r2_hidden(X30,X31)|k4_xboole_0(k2_tarski(X29,X30),X31)=k2_tarski(X29,X30))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).
% 0.39/0.63  fof(c_0_15, plain, ![X17, X18]:k1_enumset1(X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.39/0.63  fof(c_0_16, plain, ![X19, X20, X21]:k2_enumset1(X19,X19,X20,X21)=k1_enumset1(X19,X20,X21), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.39/0.63  fof(c_0_17, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),esk5_0))&((k1_mcart_1(esk2_0)!=esk3_0|~r2_hidden(k2_mcart_1(esk2_0),esk5_0))&(k1_mcart_1(esk2_0)!=esk4_0|~r2_hidden(k2_mcart_1(esk2_0),esk5_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).
% 0.39/0.63  cnf(c_0_18, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.39/0.63  cnf(c_0_19, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|k4_xboole_0(k2_tarski(X1,X3),X2)=k2_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.39/0.63  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.39/0.63  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.39/0.63  fof(c_0_22, plain, ![X32, X33, X34]:((r2_hidden(k1_mcart_1(X32),X33)|~r2_hidden(X32,k2_zfmisc_1(X33,X34)))&(r2_hidden(k2_mcart_1(X32),X34)|~r2_hidden(X32,k2_zfmisc_1(X33,X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.39/0.63  cnf(c_0_23, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),esk5_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.39/0.63  fof(c_0_24, plain, ![X26, X27, X28]:(((r2_hidden(X26,X28)|~r1_tarski(k2_tarski(X26,X27),X28))&(r2_hidden(X27,X28)|~r1_tarski(k2_tarski(X26,X27),X28)))&(~r2_hidden(X26,X28)|~r2_hidden(X27,X28)|r1_tarski(k2_tarski(X26,X27),X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.39/0.63  fof(c_0_25, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.39/0.63  cnf(c_0_26, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_18])).
% 0.39/0.63  cnf(c_0_27, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X3),X2)=k2_enumset1(X1,X1,X1,X3)|r2_hidden(X3,X2)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_20]), c_0_21]), c_0_21])).
% 0.39/0.63  cnf(c_0_28, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.39/0.63  cnf(c_0_29, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_20]), c_0_21])).
% 0.39/0.63  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.39/0.63  cnf(c_0_31, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.39/0.63  fof(c_0_32, plain, ![X22, X23, X24, X25]:(((r2_hidden(X22,X24)|~r2_hidden(k4_tarski(X22,X23),k2_zfmisc_1(X24,X25)))&(r2_hidden(X23,X25)|~r2_hidden(k4_tarski(X22,X23),k2_zfmisc_1(X24,X25))))&(~r2_hidden(X22,X24)|~r2_hidden(X23,X25)|r2_hidden(k4_tarski(X22,X23),k2_zfmisc_1(X24,X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.39/0.63  cnf(c_0_33, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.39/0.63  cnf(c_0_34, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|~r2_hidden(X4,k2_enumset1(X1,X1,X1,X3))|~r2_hidden(X4,X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.39/0.63  cnf(c_0_35, negated_conjecture, (r2_hidden(k1_mcart_1(esk2_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.39/0.63  cnf(c_0_36, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_enumset1(X1,X1,X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_20]), c_0_21])).
% 0.39/0.63  cnf(c_0_37, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_31])).
% 0.39/0.63  fof(c_0_38, plain, ![X35, X36, X37]:((k1_mcart_1(X35)=X36|~r2_hidden(X35,k2_zfmisc_1(k1_tarski(X36),X37)))&(r2_hidden(k2_mcart_1(X35),X37)|~r2_hidden(X35,k2_zfmisc_1(k1_tarski(X36),X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_mcart_1])])])).
% 0.39/0.63  fof(c_0_39, plain, ![X16]:k2_tarski(X16,X16)=k1_tarski(X16), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.39/0.63  cnf(c_0_40, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.39/0.63  cnf(c_0_41, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),esk5_0)), inference(spm,[status(thm)],[c_0_33, c_0_29])).
% 0.39/0.63  cnf(c_0_42, negated_conjecture, (r2_hidden(esk4_0,X1)|r2_hidden(esk3_0,X1)|~r2_hidden(k1_mcart_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.39/0.63  cnf(c_0_43, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.39/0.63  cnf(c_0_44, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k1_tarski(X2),X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.39/0.63  cnf(c_0_45, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.39/0.63  cnf(c_0_46, negated_conjecture, (r2_hidden(k4_tarski(X1,k2_mcart_1(esk2_0)),k2_zfmisc_1(X2,esk5_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.39/0.63  cnf(c_0_47, negated_conjecture, (r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1))|r2_hidden(esk4_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.39/0.63  fof(c_0_48, plain, ![X38, X39]:(k1_mcart_1(k4_tarski(X38,X39))=X38&k2_mcart_1(k4_tarski(X38,X39))=X39), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.39/0.63  cnf(c_0_49, negated_conjecture, (k1_mcart_1(esk2_0)!=esk4_0|~r2_hidden(k2_mcart_1(esk2_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.39/0.63  cnf(c_0_50, plain, (k1_mcart_1(X1)=X2|~r2_hidden(X1,k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_20]), c_0_21])).
% 0.39/0.63  cnf(c_0_51, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,k2_mcart_1(esk2_0)),k2_zfmisc_1(k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1),esk5_0))|r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),X1))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.39/0.63  cnf(c_0_52, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.39/0.63  cnf(c_0_53, negated_conjecture, (k1_mcart_1(esk2_0)!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_41])])).
% 0.39/0.63  cnf(c_0_54, negated_conjecture, (r2_hidden(esk3_0,k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0)))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53])).
% 0.39/0.63  cnf(c_0_55, negated_conjecture, (k1_mcart_1(esk2_0)!=esk3_0|~r2_hidden(k2_mcart_1(esk2_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.39/0.63  cnf(c_0_56, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,k2_mcart_1(esk2_0)),k2_zfmisc_1(k2_enumset1(k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0),k1_mcart_1(esk2_0)),esk5_0))), inference(spm,[status(thm)],[c_0_46, c_0_54])).
% 0.39/0.63  cnf(c_0_57, negated_conjecture, (k1_mcart_1(esk2_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_41])])).
% 0.39/0.63  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_56]), c_0_52]), c_0_57]), ['proof']).
% 0.39/0.63  # SZS output end CNFRefutation
% 0.39/0.63  # Proof object total steps             : 59
% 0.39/0.63  # Proof object clause steps            : 34
% 0.39/0.63  # Proof object formula steps           : 25
% 0.39/0.63  # Proof object conjectures             : 18
% 0.39/0.63  # Proof object clause conjectures      : 15
% 0.39/0.63  # Proof object formula conjectures     : 3
% 0.39/0.63  # Proof object initial clauses used    : 15
% 0.39/0.63  # Proof object initial formulas used   : 12
% 0.39/0.63  # Proof object generating inferences   : 11
% 0.39/0.63  # Proof object simplifying inferences  : 21
% 0.39/0.63  # Training examples: 0 positive, 0 negative
% 0.39/0.63  # Parsed axioms                        : 12
% 0.39/0.63  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.63  # Initial clauses                      : 30
% 0.39/0.63  # Removed in clause preprocessing      : 3
% 0.39/0.63  # Initial clauses in saturation        : 27
% 0.39/0.63  # Processed clauses                    : 432
% 0.39/0.63  # ...of these trivial                  : 28
% 0.39/0.63  # ...subsumed                          : 49
% 0.39/0.63  # ...remaining for further processing  : 355
% 0.39/0.63  # Other redundant clauses eliminated   : 9
% 0.39/0.63  # Clauses deleted for lack of memory   : 0
% 0.39/0.63  # Backward-subsumed                    : 1
% 0.39/0.63  # Backward-rewritten                   : 4
% 0.39/0.63  # Generated clauses                    : 13623
% 0.39/0.63  # ...of the previous two non-trivial   : 13055
% 0.39/0.63  # Contextual simplify-reflections      : 0
% 0.39/0.63  # Paramodulations                      : 13606
% 0.39/0.63  # Factorizations                       : 8
% 0.39/0.63  # Equation resolutions                 : 9
% 0.39/0.63  # Propositional unsat checks           : 0
% 0.39/0.63  #    Propositional check models        : 0
% 0.39/0.63  #    Propositional check unsatisfiable : 0
% 0.39/0.63  #    Propositional clauses             : 0
% 0.39/0.63  #    Propositional clauses after purity: 0
% 0.39/0.63  #    Propositional unsat core size     : 0
% 0.39/0.63  #    Propositional preprocessing time  : 0.000
% 0.39/0.63  #    Propositional encoding time       : 0.000
% 0.39/0.63  #    Propositional solver time         : 0.000
% 0.39/0.63  #    Success case prop preproc time    : 0.000
% 0.39/0.63  #    Success case prop encoding time   : 0.000
% 0.39/0.63  #    Success case prop solver time     : 0.000
% 0.39/0.63  # Current number of processed clauses  : 320
% 0.39/0.63  #    Positive orientable unit clauses  : 115
% 0.39/0.63  #    Positive unorientable unit clauses: 0
% 0.39/0.63  #    Negative unit clauses             : 2
% 0.39/0.63  #    Non-unit-clauses                  : 203
% 0.39/0.63  # Current number of unprocessed clauses: 12587
% 0.39/0.63  # ...number of literals in the above   : 25048
% 0.39/0.63  # Current number of archived formulas  : 0
% 0.39/0.63  # Current number of archived clauses   : 33
% 0.39/0.63  # Clause-clause subsumption calls (NU) : 2730
% 0.39/0.63  # Rec. Clause-clause subsumption calls : 2272
% 0.39/0.63  # Non-unit clause-clause subsumptions  : 50
% 0.39/0.63  # Unit Clause-clause subsumption calls : 241
% 0.39/0.63  # Rewrite failures with RHS unbound    : 0
% 0.39/0.63  # BW rewrite match attempts            : 343
% 0.39/0.63  # BW rewrite match successes           : 3
% 0.39/0.63  # Condensation attempts                : 0
% 0.39/0.63  # Condensation successes               : 0
% 0.39/0.63  # Termbank termtop insertions          : 448336
% 0.39/0.64  
% 0.39/0.64  # -------------------------------------------------
% 0.39/0.64  # User time                : 0.279 s
% 0.39/0.64  # System time              : 0.012 s
% 0.39/0.64  # Total time               : 0.291 s
% 0.39/0.64  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
