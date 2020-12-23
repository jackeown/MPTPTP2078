%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:11 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 236 expanded)
%              Number of clauses        :   47 ( 119 expanded)
%              Number of leaves         :   10 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  159 ( 620 expanded)
%              Number of equality atoms :   49 ( 241 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t82_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) = k1_zfmisc_1(k2_xboole_0(X1,X2))
     => r3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_zfmisc_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d9_xboole_0,axiom,(
    ! [X1,X2] :
      ( r3_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        | r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

fof(c_0_10,plain,(
    ! [X42,X43] : k3_tarski(k2_tarski(X42,X43)) = k2_xboole_0(X42,X43) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X33,X34] : k1_enumset1(X33,X33,X34) = k2_tarski(X33,X34) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) = k1_zfmisc_1(k2_xboole_0(X1,X2))
       => r3_xboole_0(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t82_zfmisc_1])).

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
    ! [X35,X36,X37,X38,X39,X40] :
      ( ( ~ r2_hidden(X37,X36)
        | r1_tarski(X37,X35)
        | X36 != k1_zfmisc_1(X35) )
      & ( ~ r1_tarski(X38,X35)
        | r2_hidden(X38,X36)
        | X36 != k1_zfmisc_1(X35) )
      & ( ~ r2_hidden(esk3_2(X39,X40),X40)
        | ~ r1_tarski(esk3_2(X39,X40),X39)
        | X40 = k1_zfmisc_1(X39) )
      & ( r2_hidden(esk3_2(X39,X40),X40)
        | r1_tarski(esk3_2(X39,X40),X39)
        | X40 = k1_zfmisc_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_15,plain,(
    ! [X18,X19,X20] : k4_xboole_0(k4_xboole_0(X18,X19),X20) = k4_xboole_0(X18,k2_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_16,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,negated_conjecture,
    ( k2_xboole_0(k1_zfmisc_1(esk4_0),k1_zfmisc_1(esk5_0)) = k1_zfmisc_1(k2_xboole_0(esk4_0,esk5_0))
    & ~ r3_xboole_0(esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_22,plain,(
    ! [X23,X24] : k2_tarski(X23,X24) = k2_tarski(X24,X23) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_23,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( k2_xboole_0(k1_zfmisc_1(esk4_0),k1_zfmisc_1(esk5_0)) = k1_zfmisc_1(k2_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k3_tarski(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( k3_tarski(k1_enumset1(k1_zfmisc_1(esk4_0),k1_zfmisc_1(esk4_0),k1_zfmisc_1(esk5_0))) = k1_zfmisc_1(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_24]),c_0_24])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k4_xboole_0(k1_zfmisc_1(X2),X3))
    | r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_17]),c_0_17])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( k4_xboole_0(X1,k1_zfmisc_1(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)))) = k4_xboole_0(k4_xboole_0(X1,k1_zfmisc_1(esk4_0)),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k4_xboole_0(k1_zfmisc_1(X1),X2))
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k4_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_35]),c_0_31])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,k1_zfmisc_1(esk4_0)),k1_zfmisc_1(esk5_0)))
    | ~ r2_hidden(X1,k1_zfmisc_1(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k4_xboole_0(k4_xboole_0(k1_zfmisc_1(X1),X2),X3))
    | r2_hidden(X1,X2)
    | r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_39])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_37,c_0_40])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1))
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_39])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(esk5_0))
    | r2_hidden(X1,k1_zfmisc_1(esk4_0))
    | ~ r2_hidden(X1,k1_zfmisc_1(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_45])).

fof(c_0_49,plain,(
    ! [X21,X22] : r1_tarski(X21,k2_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),k1_zfmisc_1(esk4_0))
    | r2_hidden(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),esk5_0)
    | r2_hidden(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_52,c_0_24])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),esk5_0)
    | r1_tarski(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_53])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_35])).

fof(c_0_58,plain,(
    ! [X16,X17] :
      ( ( ~ r3_xboole_0(X16,X17)
        | r1_tarski(X16,X17)
        | r1_tarski(X17,X16) )
      & ( ~ r1_tarski(X16,X17)
        | r3_xboole_0(X16,X17) )
      & ( ~ r1_tarski(X17,X16)
        | r3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).

cnf(c_0_59,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)) = esk5_0
    | r1_tarski(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_60,negated_conjecture,
    ( ~ r3_xboole_0(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_61,plain,
    ( r3_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)) = esk5_0
    | k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_59]),c_0_54])])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,plain,
    ( r3_xboole_0(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)) = esk4_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_62]),c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tarski(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_65]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 14:59:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.47/0.63  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.47/0.63  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.47/0.63  #
% 0.47/0.63  # Preprocessing time       : 0.028 s
% 0.47/0.63  # Presaturation interreduction done
% 0.47/0.63  
% 0.47/0.63  # Proof found!
% 0.47/0.63  # SZS status Theorem
% 0.47/0.63  # SZS output start CNFRefutation
% 0.47/0.63  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.47/0.63  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.47/0.63  fof(t82_zfmisc_1, conjecture, ![X1, X2]:(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2))=k1_zfmisc_1(k2_xboole_0(X1,X2))=>r3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_zfmisc_1)).
% 0.47/0.63  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.47/0.63  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.47/0.63  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.47/0.63  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.47/0.63  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.47/0.63  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.47/0.63  fof(d9_xboole_0, axiom, ![X1, X2]:(r3_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)|r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_xboole_0)).
% 0.47/0.63  fof(c_0_10, plain, ![X42, X43]:k3_tarski(k2_tarski(X42,X43))=k2_xboole_0(X42,X43), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.47/0.63  fof(c_0_11, plain, ![X33, X34]:k1_enumset1(X33,X33,X34)=k2_tarski(X33,X34), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.47/0.63  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2))=k1_zfmisc_1(k2_xboole_0(X1,X2))=>r3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t82_zfmisc_1])).
% 0.47/0.63  fof(c_0_13, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.47/0.63  fof(c_0_14, plain, ![X35, X36, X37, X38, X39, X40]:(((~r2_hidden(X37,X36)|r1_tarski(X37,X35)|X36!=k1_zfmisc_1(X35))&(~r1_tarski(X38,X35)|r2_hidden(X38,X36)|X36!=k1_zfmisc_1(X35)))&((~r2_hidden(esk3_2(X39,X40),X40)|~r1_tarski(esk3_2(X39,X40),X39)|X40=k1_zfmisc_1(X39))&(r2_hidden(esk3_2(X39,X40),X40)|r1_tarski(esk3_2(X39,X40),X39)|X40=k1_zfmisc_1(X39)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.47/0.63  fof(c_0_15, plain, ![X18, X19, X20]:k4_xboole_0(k4_xboole_0(X18,X19),X20)=k4_xboole_0(X18,k2_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.47/0.63  cnf(c_0_16, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.63  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.47/0.63  fof(c_0_18, negated_conjecture, (k2_xboole_0(k1_zfmisc_1(esk4_0),k1_zfmisc_1(esk5_0))=k1_zfmisc_1(k2_xboole_0(esk4_0,esk5_0))&~r3_xboole_0(esk4_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.47/0.63  cnf(c_0_19, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.63  cnf(c_0_20, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.47/0.63  fof(c_0_21, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.47/0.63  fof(c_0_22, plain, ![X23, X24]:k2_tarski(X23,X24)=k2_tarski(X24,X23), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.47/0.63  cnf(c_0_23, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.47/0.63  cnf(c_0_24, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.47/0.63  cnf(c_0_25, negated_conjecture, (k2_xboole_0(k1_zfmisc_1(esk4_0),k1_zfmisc_1(esk5_0))=k1_zfmisc_1(k2_xboole_0(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.63  cnf(c_0_26, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_19])).
% 0.47/0.63  cnf(c_0_27, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_20])).
% 0.47/0.63  cnf(c_0_28, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.47/0.63  cnf(c_0_29, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.47/0.63  cnf(c_0_30, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.63  cnf(c_0_31, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k3_tarski(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.47/0.63  cnf(c_0_32, negated_conjecture, (k3_tarski(k1_enumset1(k1_zfmisc_1(esk4_0),k1_zfmisc_1(esk4_0),k1_zfmisc_1(esk5_0)))=k1_zfmisc_1(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_24]), c_0_24])).
% 0.47/0.63  cnf(c_0_33, plain, (r2_hidden(X1,k4_xboole_0(k1_zfmisc_1(X2),X3))|r2_hidden(X1,X3)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.47/0.63  cnf(c_0_34, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_28])).
% 0.47/0.63  cnf(c_0_35, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_17]), c_0_17])).
% 0.47/0.63  cnf(c_0_36, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.63  cnf(c_0_37, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_30])).
% 0.47/0.63  cnf(c_0_38, negated_conjecture, (k4_xboole_0(X1,k1_zfmisc_1(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0))))=k4_xboole_0(k4_xboole_0(X1,k1_zfmisc_1(esk4_0)),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.47/0.63  cnf(c_0_39, plain, (r2_hidden(X1,k4_xboole_0(k1_zfmisc_1(X1),X2))|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.47/0.63  cnf(c_0_40, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k4_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_35]), c_0_31])).
% 0.47/0.63  cnf(c_0_41, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_36])).
% 0.47/0.63  cnf(c_0_42, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,k1_zfmisc_1(esk4_0)),k1_zfmisc_1(esk5_0)))|~r2_hidden(X1,k1_zfmisc_1(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0))))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.47/0.63  cnf(c_0_43, plain, (r2_hidden(X1,k4_xboole_0(k4_xboole_0(k1_zfmisc_1(X1),X2),X3))|r2_hidden(X1,X2)|r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_26, c_0_39])).
% 0.47/0.63  cnf(c_0_44, plain, (~r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_37, c_0_40])).
% 0.47/0.63  cnf(c_0_45, plain, (r2_hidden(X1,k1_zfmisc_1(X1))|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_39])).
% 0.47/0.63  cnf(c_0_46, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.47/0.63  cnf(c_0_47, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(esk5_0))|r2_hidden(X1,k1_zfmisc_1(esk4_0))|~r2_hidden(X1,k1_zfmisc_1(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0))))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.47/0.63  cnf(c_0_48, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_45])).
% 0.47/0.63  fof(c_0_49, plain, ![X21, X22]:r1_tarski(X21,k2_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.47/0.63  cnf(c_0_50, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_46])).
% 0.47/0.63  cnf(c_0_51, negated_conjecture, (r2_hidden(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),k1_zfmisc_1(esk4_0))|r2_hidden(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.47/0.63  cnf(c_0_52, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.47/0.63  cnf(c_0_53, negated_conjecture, (r1_tarski(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),esk5_0)|r2_hidden(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.47/0.63  cnf(c_0_54, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_52, c_0_24])).
% 0.47/0.63  cnf(c_0_55, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.47/0.63  cnf(c_0_56, negated_conjecture, (r1_tarski(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),esk5_0)|r1_tarski(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),esk4_0)), inference(spm,[status(thm)],[c_0_50, c_0_53])).
% 0.47/0.63  cnf(c_0_57, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X1)))), inference(spm,[status(thm)],[c_0_54, c_0_35])).
% 0.47/0.63  fof(c_0_58, plain, ![X16, X17]:((~r3_xboole_0(X16,X17)|(r1_tarski(X16,X17)|r1_tarski(X17,X16)))&((~r1_tarski(X16,X17)|r3_xboole_0(X16,X17))&(~r1_tarski(X17,X16)|r3_xboole_0(X16,X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).
% 0.47/0.63  cnf(c_0_59, negated_conjecture, (k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0))=esk5_0|r1_tarski(k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 0.47/0.63  cnf(c_0_60, negated_conjecture, (~r3_xboole_0(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.63  cnf(c_0_61, plain, (r3_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.47/0.63  cnf(c_0_62, negated_conjecture, (k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0))=esk5_0|k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_59]), c_0_54])])).
% 0.47/0.63  cnf(c_0_63, negated_conjecture, (~r1_tarski(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.47/0.63  cnf(c_0_64, plain, (r3_xboole_0(X2,X1)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.47/0.63  cnf(c_0_65, negated_conjecture, (k3_tarski(k1_enumset1(esk4_0,esk4_0,esk5_0))=esk4_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_62]), c_0_63])).
% 0.47/0.63  cnf(c_0_66, negated_conjecture, (~r1_tarski(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_60, c_0_64])).
% 0.47/0.63  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_65]), c_0_66]), ['proof']).
% 0.47/0.63  # SZS output end CNFRefutation
% 0.47/0.63  # Proof object total steps             : 68
% 0.47/0.63  # Proof object clause steps            : 47
% 0.47/0.63  # Proof object formula steps           : 21
% 0.47/0.63  # Proof object conjectures             : 18
% 0.47/0.63  # Proof object clause conjectures      : 15
% 0.47/0.63  # Proof object formula conjectures     : 3
% 0.47/0.63  # Proof object initial clauses used    : 16
% 0.47/0.63  # Proof object initial formulas used   : 10
% 0.47/0.63  # Proof object generating inferences   : 20
% 0.47/0.63  # Proof object simplifying inferences  : 21
% 0.47/0.63  # Training examples: 0 positive, 0 negative
% 0.47/0.63  # Parsed axioms                        : 12
% 0.47/0.63  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.63  # Initial clauses                      : 28
% 0.47/0.63  # Removed in clause preprocessing      : 3
% 0.47/0.63  # Initial clauses in saturation        : 25
% 0.47/0.63  # Processed clauses                    : 811
% 0.47/0.63  # ...of these trivial                  : 5
% 0.47/0.63  # ...subsumed                          : 494
% 0.47/0.63  # ...remaining for further processing  : 312
% 0.47/0.63  # Other redundant clauses eliminated   : 47
% 0.47/0.63  # Clauses deleted for lack of memory   : 0
% 0.47/0.63  # Backward-subsumed                    : 34
% 0.47/0.63  # Backward-rewritten                   : 95
% 0.47/0.63  # Generated clauses                    : 15635
% 0.47/0.63  # ...of the previous two non-trivial   : 15378
% 0.47/0.63  # Contextual simplify-reflections      : 2
% 0.47/0.63  # Paramodulations                      : 15556
% 0.47/0.63  # Factorizations                       : 33
% 0.47/0.63  # Equation resolutions                 : 47
% 0.47/0.63  # Propositional unsat checks           : 0
% 0.47/0.63  #    Propositional check models        : 0
% 0.47/0.63  #    Propositional check unsatisfiable : 0
% 0.47/0.63  #    Propositional clauses             : 0
% 0.47/0.63  #    Propositional clauses after purity: 0
% 0.47/0.63  #    Propositional unsat core size     : 0
% 0.47/0.63  #    Propositional preprocessing time  : 0.000
% 0.47/0.63  #    Propositional encoding time       : 0.000
% 0.47/0.63  #    Propositional solver time         : 0.000
% 0.47/0.63  #    Success case prop preproc time    : 0.000
% 0.47/0.63  #    Success case prop encoding time   : 0.000
% 0.47/0.63  #    Success case prop solver time     : 0.000
% 0.47/0.63  # Current number of processed clauses  : 150
% 0.47/0.63  #    Positive orientable unit clauses  : 9
% 0.47/0.63  #    Positive unorientable unit clauses: 2
% 0.47/0.63  #    Negative unit clauses             : 3
% 0.47/0.63  #    Non-unit-clauses                  : 136
% 0.47/0.64  # Current number of unprocessed clauses: 14366
% 0.47/0.64  # ...number of literals in the above   : 71652
% 0.47/0.64  # Current number of archived formulas  : 0
% 0.47/0.64  # Current number of archived clauses   : 156
% 0.47/0.64  # Clause-clause subsumption calls (NU) : 14251
% 0.47/0.64  # Rec. Clause-clause subsumption calls : 9434
% 0.47/0.64  # Non-unit clause-clause subsumptions  : 524
% 0.47/0.64  # Unit Clause-clause subsumption calls : 92
% 0.47/0.64  # Rewrite failures with RHS unbound    : 0
% 0.47/0.64  # BW rewrite match attempts            : 78
% 0.47/0.64  # BW rewrite match successes           : 61
% 0.47/0.64  # Condensation attempts                : 0
% 0.47/0.64  # Condensation successes               : 0
% 0.47/0.64  # Termbank termtop insertions          : 338178
% 0.47/0.64  
% 0.47/0.64  # -------------------------------------------------
% 0.47/0.64  # User time                : 0.260 s
% 0.47/0.64  # System time              : 0.018 s
% 0.47/0.64  # Total time               : 0.278 s
% 0.47/0.64  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
