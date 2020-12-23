%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:25 EST 2020

% Result     : Theorem 1.31s
% Output     : CNFRefutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   85 (86340 expanded)
%              Number of clauses        :   68 (40736 expanded)
%              Number of leaves         :    8 (21962 expanded)
%              Depth                    :   29
%              Number of atoms          :  241 (311272 expanded)
%              Number of equality atoms :   80 (140676 expanded)
%              Maximal formula depth    :   23 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t113_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_8,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk1_3(X16,X17,X18),X16)
        | r2_hidden(esk1_3(X16,X17,X18),X17)
        | X18 = k4_xboole_0(X16,X17) )
      & ( r2_hidden(esk1_3(X16,X17,X18),X16)
        | r2_hidden(esk1_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk1_3(X16,X17,X18),X17)
        | r2_hidden(esk1_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_9,plain,(
    ! [X20,X21] : k4_xboole_0(X20,X21) = k5_xboole_0(X20,k3_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,negated_conjecture,
    ( ( esk7_0 != k1_xboole_0
      | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 )
    & ( esk8_0 != k1_xboole_0
      | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0
      | esk7_0 = k1_xboole_0
      | esk8_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

fof(c_0_14,plain,(
    ! [X24,X25,X26,X27,X30,X31,X32,X33,X34,X35,X37,X38] :
      ( ( r2_hidden(esk2_4(X24,X25,X26,X27),X24)
        | ~ r2_hidden(X27,X26)
        | X26 != k2_zfmisc_1(X24,X25) )
      & ( r2_hidden(esk3_4(X24,X25,X26,X27),X25)
        | ~ r2_hidden(X27,X26)
        | X26 != k2_zfmisc_1(X24,X25) )
      & ( X27 = k4_tarski(esk2_4(X24,X25,X26,X27),esk3_4(X24,X25,X26,X27))
        | ~ r2_hidden(X27,X26)
        | X26 != k2_zfmisc_1(X24,X25) )
      & ( ~ r2_hidden(X31,X24)
        | ~ r2_hidden(X32,X25)
        | X30 != k4_tarski(X31,X32)
        | r2_hidden(X30,X26)
        | X26 != k2_zfmisc_1(X24,X25) )
      & ( ~ r2_hidden(esk4_3(X33,X34,X35),X35)
        | ~ r2_hidden(X37,X33)
        | ~ r2_hidden(X38,X34)
        | esk4_3(X33,X34,X35) != k4_tarski(X37,X38)
        | X35 = k2_zfmisc_1(X33,X34) )
      & ( r2_hidden(esk5_3(X33,X34,X35),X33)
        | r2_hidden(esk4_3(X33,X34,X35),X35)
        | X35 = k2_zfmisc_1(X33,X34) )
      & ( r2_hidden(esk6_3(X33,X34,X35),X34)
        | r2_hidden(esk4_3(X33,X34,X35),X35)
        | X35 = k2_zfmisc_1(X33,X34) )
      & ( esk4_3(X33,X34,X35) = k4_tarski(esk5_3(X33,X34,X35),esk6_3(X33,X34,X35))
        | r2_hidden(esk4_3(X33,X34,X35),X35)
        | X35 = k2_zfmisc_1(X33,X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_16,plain,(
    ! [X22] : k3_xboole_0(X22,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_17,plain,(
    ! [X23] : k5_xboole_0(X23,k1_xboole_0) = X23 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_18,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( esk8_0 != k1_xboole_0
    | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_15,c_0_12])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk6_3(esk7_0,esk8_0,k1_xboole_0),esk8_0)
    | r2_hidden(esk4_3(esk7_0,esk8_0,k1_xboole_0),k1_xboole_0)
    | esk8_0 != k1_xboole_0 ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20])])).

cnf(c_0_26,plain,
    ( X1 = X2
    | r2_hidden(esk1_3(X2,k1_xboole_0,X1),X2)
    | r2_hidden(esk1_3(X2,k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

fof(c_0_27,plain,(
    ! [X9,X10] : k5_xboole_0(X9,X10) = k5_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_28,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_22]),c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_3(esk8_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk1_3(esk8_0,k1_xboole_0,k1_xboole_0),esk8_0)
    | r2_hidden(esk4_3(esk7_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk6_3(esk7_0,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_29,c_0_12])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk4_3(esk7_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk1_3(esk8_0,k1_xboole_0,k1_xboole_0),esk8_0)
    | r2_hidden(esk1_3(esk8_0,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_31])).

cnf(c_0_36,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_23,c_0_32])).

cnf(c_0_37,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_33])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk1_3(esk8_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk1_3(esk8_0,k1_xboole_0,k1_xboole_0),esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_35]),c_0_35])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,X2,X1),k1_xboole_0)
    | r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_21]),c_0_37])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_33])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(X4,X3)
    | ~ r2_hidden(X4,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk1_3(k1_xboole_0,X1,esk8_0),esk8_0)
    | r2_hidden(esk1_3(k1_xboole_0,X1,esk8_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( r2_hidden(esk1_3(X1,X1,X2),X1)
    | r2_hidden(esk1_3(X1,X1,X2),X2)
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_21]),c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_3(k1_xboole_0,X1,esk8_0),k1_xboole_0)
    | r2_hidden(esk1_3(k1_xboole_0,X1,esk8_0),esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_43]),c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk1_3(k1_xboole_0,X1,esk8_0),k1_xboole_0)
    | r2_hidden(esk1_3(X2,X2,esk8_0),esk8_0)
    | r2_hidden(esk1_3(X2,X2,esk8_0),X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_3(esk8_0,esk8_0,esk8_0),esk8_0)
    | r2_hidden(esk1_3(k1_xboole_0,X1,esk8_0),k1_xboole_0) ),
    inference(ef,[status(thm)],[c_0_46])).

cnf(c_0_48,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_3(esk8_0,esk8_0,esk8_0),esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_47]),c_0_47])).

cnf(c_0_50,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_48,c_0_12])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X1,esk8_0),esk8_0)
    | r2_hidden(esk1_3(X1,X1,esk8_0),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_49])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_33])).

cnf(c_0_53,negated_conjecture,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = esk8_0
    | r2_hidden(esk1_3(X1,X1,esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X1,esk8_0),esk8_0)
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X1,esk8_0),esk8_0)
    | ~ r2_hidden(X2,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_53]),c_0_54])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_26])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X2,esk8_0),esk8_0)
    | r2_hidden(esk1_3(X1,X2,esk8_0),X1)
    | ~ r2_hidden(esk1_3(esk8_0,esk8_0,esk8_0),X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X1,esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | k2_zfmisc_1(esk7_0,esk8_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_60,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X1)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_61,plain,
    ( r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),X1)
    | ~ r2_hidden(X2,k3_xboole_0(X3,X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_52,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk1_3(X1,esk8_0,esk8_0),esk8_0)
    | r2_hidden(esk1_3(X1,esk8_0,esk8_0),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk5_3(esk7_0,esk8_0,k1_xboole_0),esk7_0)
    | r2_hidden(esk4_3(esk7_0,esk8_0,k1_xboole_0),k1_xboole_0)
    | esk7_0 != k1_xboole_0 ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60])])).

cnf(c_0_65,plain,
    ( r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_37])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk1_3(k5_xboole_0(X1,k3_xboole_0(X2,X1)),esk8_0,esk8_0),esk8_0)
    | ~ r2_hidden(esk1_3(k5_xboole_0(X1,k3_xboole_0(X2,X1)),esk8_0,esk8_0),X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_62])).

cnf(c_0_67,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_63])])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_26])]),c_0_65]),c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk1_3(k1_xboole_0,esk8_0,esk8_0),esk8_0)
    | ~ r2_hidden(esk1_3(k1_xboole_0,esk8_0,esk8_0),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_hidden(esk1_3(X1,esk8_0,esk8_0),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_62]),c_0_30])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),X1),k2_zfmisc_1(esk7_0,X2))
    | r2_hidden(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk1_3(k1_xboole_0,esk8_0,esk8_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_62]),c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),esk1_3(k1_xboole_0,esk8_0,esk8_0)),k2_zfmisc_1(esk7_0,esk8_0))
    | r2_hidden(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_74,negated_conjecture,
    ( k2_zfmisc_1(esk7_0,esk8_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(k4_tarski(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),esk1_3(k1_xboole_0,esk8_0,esk8_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( ~ r2_hidden(esk1_3(X1,X1,esk8_0),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_51]),c_0_30])).

cnf(c_0_77,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(esk1_3(X1,X1,k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_79,plain,
    ( r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_80,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_77]),c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),X1)
    | ~ r2_hidden(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_68]),c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_83]),c_0_83])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.31/1.48  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 1.31/1.48  # and selection function SelectNegativeLiterals.
% 1.31/1.48  #
% 1.31/1.48  # Preprocessing time       : 0.027 s
% 1.31/1.48  # Presaturation interreduction done
% 1.31/1.48  
% 1.31/1.48  # Proof found!
% 1.31/1.48  # SZS status Theorem
% 1.31/1.48  # SZS output start CNFRefutation
% 1.31/1.48  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.31/1.48  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.31/1.48  fof(t113_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.31/1.48  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 1.31/1.48  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.31/1.48  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 1.31/1.48  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 1.31/1.48  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.31/1.48  fof(c_0_8, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk1_3(X16,X17,X18),X18)|(~r2_hidden(esk1_3(X16,X17,X18),X16)|r2_hidden(esk1_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk1_3(X16,X17,X18),X16)|r2_hidden(esk1_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk1_3(X16,X17,X18),X17)|r2_hidden(esk1_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 1.31/1.48  fof(c_0_9, plain, ![X20, X21]:k4_xboole_0(X20,X21)=k5_xboole_0(X20,k3_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.31/1.48  fof(c_0_10, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t113_zfmisc_1])).
% 1.31/1.48  cnf(c_0_11, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.31/1.48  cnf(c_0_12, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.31/1.48  fof(c_0_13, negated_conjecture, (((esk7_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0)&(esk8_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0))&(k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0|(esk7_0=k1_xboole_0|esk8_0=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 1.31/1.48  fof(c_0_14, plain, ![X24, X25, X26, X27, X30, X31, X32, X33, X34, X35, X37, X38]:(((((r2_hidden(esk2_4(X24,X25,X26,X27),X24)|~r2_hidden(X27,X26)|X26!=k2_zfmisc_1(X24,X25))&(r2_hidden(esk3_4(X24,X25,X26,X27),X25)|~r2_hidden(X27,X26)|X26!=k2_zfmisc_1(X24,X25)))&(X27=k4_tarski(esk2_4(X24,X25,X26,X27),esk3_4(X24,X25,X26,X27))|~r2_hidden(X27,X26)|X26!=k2_zfmisc_1(X24,X25)))&(~r2_hidden(X31,X24)|~r2_hidden(X32,X25)|X30!=k4_tarski(X31,X32)|r2_hidden(X30,X26)|X26!=k2_zfmisc_1(X24,X25)))&((~r2_hidden(esk4_3(X33,X34,X35),X35)|(~r2_hidden(X37,X33)|~r2_hidden(X38,X34)|esk4_3(X33,X34,X35)!=k4_tarski(X37,X38))|X35=k2_zfmisc_1(X33,X34))&(((r2_hidden(esk5_3(X33,X34,X35),X33)|r2_hidden(esk4_3(X33,X34,X35),X35)|X35=k2_zfmisc_1(X33,X34))&(r2_hidden(esk6_3(X33,X34,X35),X34)|r2_hidden(esk4_3(X33,X34,X35),X35)|X35=k2_zfmisc_1(X33,X34)))&(esk4_3(X33,X34,X35)=k4_tarski(esk5_3(X33,X34,X35),esk6_3(X33,X34,X35))|r2_hidden(esk4_3(X33,X34,X35),X35)|X35=k2_zfmisc_1(X33,X34))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 1.31/1.48  cnf(c_0_15, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.31/1.48  fof(c_0_16, plain, ![X22]:k3_xboole_0(X22,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 1.31/1.48  fof(c_0_17, plain, ![X23]:k5_xboole_0(X23,k1_xboole_0)=X23, inference(variable_rename,[status(thm)],[t5_boole])).
% 1.31/1.48  cnf(c_0_18, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 1.31/1.48  cnf(c_0_19, negated_conjecture, (esk8_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.31/1.48  cnf(c_0_20, plain, (r2_hidden(esk6_3(X1,X2,X3),X2)|r2_hidden(esk4_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.31/1.48  cnf(c_0_21, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_15, c_0_12])).
% 1.31/1.48  cnf(c_0_22, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.31/1.48  cnf(c_0_23, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.31/1.48  cnf(c_0_24, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_18])).
% 1.31/1.48  cnf(c_0_25, negated_conjecture, (r2_hidden(esk6_3(esk7_0,esk8_0,k1_xboole_0),esk8_0)|r2_hidden(esk4_3(esk7_0,esk8_0,k1_xboole_0),k1_xboole_0)|esk8_0!=k1_xboole_0), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20])])).
% 1.31/1.48  cnf(c_0_26, plain, (X1=X2|r2_hidden(esk1_3(X2,k1_xboole_0,X1),X2)|r2_hidden(esk1_3(X2,k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 1.31/1.48  fof(c_0_27, plain, ![X9, X10]:k5_xboole_0(X9,X10)=k5_xboole_0(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 1.31/1.48  fof(c_0_28, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.31/1.48  cnf(c_0_29, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.31/1.48  cnf(c_0_30, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_22]), c_0_23])).
% 1.31/1.48  cnf(c_0_31, negated_conjecture, (r2_hidden(esk1_3(esk8_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)|r2_hidden(esk1_3(esk8_0,k1_xboole_0,k1_xboole_0),esk8_0)|r2_hidden(esk4_3(esk7_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)|r2_hidden(esk6_3(esk7_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26])])).
% 1.31/1.48  cnf(c_0_32, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.31/1.48  cnf(c_0_33, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.31/1.48  cnf(c_0_34, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_29, c_0_12])).
% 1.31/1.48  cnf(c_0_35, negated_conjecture, (r2_hidden(esk4_3(esk7_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)|r2_hidden(esk1_3(esk8_0,k1_xboole_0,k1_xboole_0),esk8_0)|r2_hidden(esk1_3(esk8_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_31])).
% 1.31/1.48  cnf(c_0_36, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_23, c_0_32])).
% 1.31/1.48  cnf(c_0_37, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_33])).
% 1.31/1.48  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_34])).
% 1.31/1.48  cnf(c_0_39, negated_conjecture, (r2_hidden(esk1_3(esk8_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)|r2_hidden(esk1_3(esk8_0,k1_xboole_0,k1_xboole_0),esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_35]), c_0_35])).
% 1.31/1.48  cnf(c_0_40, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,X2,X1),k1_xboole_0)|r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_21]), c_0_37])).
% 1.31/1.48  cnf(c_0_41, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_38, c_0_33])).
% 1.31/1.48  cnf(c_0_42, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(X4,X3)|~r2_hidden(X4,X2)), inference(spm,[status(thm)],[c_0_24, c_0_21])).
% 1.31/1.48  cnf(c_0_43, negated_conjecture, (r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)|r2_hidden(esk1_3(k1_xboole_0,X1,esk8_0),esk8_0)|r2_hidden(esk1_3(k1_xboole_0,X1,esk8_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 1.31/1.48  cnf(c_0_44, plain, (r2_hidden(esk1_3(X1,X1,X2),X1)|r2_hidden(esk1_3(X1,X1,X2),X2)|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_21]), c_0_42])).
% 1.31/1.48  cnf(c_0_45, negated_conjecture, (r2_hidden(esk1_3(k1_xboole_0,X1,esk8_0),k1_xboole_0)|r2_hidden(esk1_3(k1_xboole_0,X1,esk8_0),esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_43]), c_0_43])).
% 1.31/1.48  cnf(c_0_46, negated_conjecture, (r2_hidden(esk1_3(k1_xboole_0,X1,esk8_0),k1_xboole_0)|r2_hidden(esk1_3(X2,X2,esk8_0),esk8_0)|r2_hidden(esk1_3(X2,X2,esk8_0),X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 1.31/1.48  cnf(c_0_47, negated_conjecture, (r2_hidden(esk1_3(esk8_0,esk8_0,esk8_0),esk8_0)|r2_hidden(esk1_3(k1_xboole_0,X1,esk8_0),k1_xboole_0)), inference(ef,[status(thm)],[c_0_46])).
% 1.31/1.48  cnf(c_0_48, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.31/1.48  cnf(c_0_49, negated_conjecture, (r2_hidden(esk1_3(esk8_0,esk8_0,esk8_0),esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_47]), c_0_47])).
% 1.31/1.48  cnf(c_0_50, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_48, c_0_12])).
% 1.31/1.48  cnf(c_0_51, negated_conjecture, (r2_hidden(esk1_3(X1,X1,esk8_0),esk8_0)|r2_hidden(esk1_3(X1,X1,esk8_0),X1)), inference(spm,[status(thm)],[c_0_44, c_0_49])).
% 1.31/1.48  cnf(c_0_52, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_24, c_0_33])).
% 1.31/1.48  cnf(c_0_53, negated_conjecture, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=esk8_0|r2_hidden(esk1_3(X1,X1,esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 1.31/1.48  cnf(c_0_54, negated_conjecture, (r2_hidden(esk1_3(X1,X1,esk8_0),esk8_0)|~r2_hidden(X2,esk8_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 1.31/1.48  cnf(c_0_55, negated_conjecture, (r2_hidden(esk1_3(X1,X1,esk8_0),esk8_0)|~r2_hidden(X2,esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_53]), c_0_54])).
% 1.31/1.48  cnf(c_0_56, plain, (k5_xboole_0(X1,X2)=X2|r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_36, c_0_26])).
% 1.31/1.48  cnf(c_0_57, negated_conjecture, (r2_hidden(esk1_3(X1,X2,esk8_0),esk8_0)|r2_hidden(esk1_3(X1,X2,esk8_0),X1)|~r2_hidden(esk1_3(esk8_0,esk8_0,esk8_0),X2)), inference(spm,[status(thm)],[c_0_42, c_0_49])).
% 1.31/1.48  cnf(c_0_58, negated_conjecture, (r2_hidden(esk1_3(X1,X1,esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_55, c_0_49])).
% 1.31/1.48  cnf(c_0_59, negated_conjecture, (esk7_0!=k1_xboole_0|k2_zfmisc_1(esk7_0,esk8_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.31/1.48  cnf(c_0_60, plain, (r2_hidden(esk5_3(X1,X2,X3),X1)|r2_hidden(esk4_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.31/1.48  cnf(c_0_61, plain, (r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),X1)|~r2_hidden(X2,k3_xboole_0(X3,X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_52, c_0_56])).
% 1.31/1.48  cnf(c_0_62, negated_conjecture, (r2_hidden(esk1_3(X1,esk8_0,esk8_0),esk8_0)|r2_hidden(esk1_3(X1,esk8_0,esk8_0),X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 1.31/1.48  cnf(c_0_63, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.31/1.48  cnf(c_0_64, negated_conjecture, (r2_hidden(esk5_3(esk7_0,esk8_0,k1_xboole_0),esk7_0)|r2_hidden(esk4_3(esk7_0,esk8_0,k1_xboole_0),k1_xboole_0)|esk7_0!=k1_xboole_0), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60])])).
% 1.31/1.48  cnf(c_0_65, plain, (r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),X1)|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_61, c_0_37])).
% 1.31/1.48  cnf(c_0_66, negated_conjecture, (r2_hidden(esk1_3(k5_xboole_0(X1,k3_xboole_0(X2,X1)),esk8_0,esk8_0),esk8_0)|~r2_hidden(esk1_3(k5_xboole_0(X1,k3_xboole_0(X2,X1)),esk8_0,esk8_0),X2)), inference(spm,[status(thm)],[c_0_52, c_0_62])).
% 1.31/1.48  cnf(c_0_67, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_63])])).
% 1.31/1.48  cnf(c_0_68, negated_conjecture, (r2_hidden(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)|r2_hidden(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_26])]), c_0_65]), c_0_65])).
% 1.31/1.48  cnf(c_0_69, negated_conjecture, (r2_hidden(esk1_3(k1_xboole_0,esk8_0,esk8_0),esk8_0)|~r2_hidden(esk1_3(k1_xboole_0,esk8_0,esk8_0),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_22]), c_0_23]), c_0_23])).
% 1.31/1.48  cnf(c_0_70, negated_conjecture, (~r2_hidden(esk1_3(X1,esk8_0,esk8_0),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_62]), c_0_30])).
% 1.31/1.48  cnf(c_0_71, negated_conjecture, (r2_hidden(k4_tarski(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),X1),k2_zfmisc_1(esk7_0,X2))|r2_hidden(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 1.31/1.48  cnf(c_0_72, negated_conjecture, (r2_hidden(esk1_3(k1_xboole_0,esk8_0,esk8_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_62]), c_0_70])).
% 1.31/1.48  cnf(c_0_73, negated_conjecture, (r2_hidden(k4_tarski(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),esk1_3(k1_xboole_0,esk8_0,esk8_0)),k2_zfmisc_1(esk7_0,esk8_0))|r2_hidden(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 1.31/1.48  cnf(c_0_74, negated_conjecture, (k2_zfmisc_1(esk7_0,esk8_0)=k1_xboole_0|esk7_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.31/1.48  cnf(c_0_75, negated_conjecture, (r2_hidden(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~r2_hidden(k4_tarski(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),esk1_3(k1_xboole_0,esk8_0,esk8_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_73])).
% 1.31/1.48  cnf(c_0_76, negated_conjecture, (~r2_hidden(esk1_3(X1,X1,esk8_0),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_51]), c_0_30])).
% 1.31/1.48  cnf(c_0_77, negated_conjecture, (esk8_0=k1_xboole_0|esk7_0=k1_xboole_0|r2_hidden(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])).
% 1.31/1.48  cnf(c_0_78, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)|~r2_hidden(esk1_3(X1,X1,k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 1.31/1.48  cnf(c_0_79, plain, (r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),X1)|~r2_hidden(X2,X1)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_30, c_0_26])).
% 1.31/1.48  cnf(c_0_80, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_77]), c_0_78])).
% 1.31/1.48  cnf(c_0_81, negated_conjecture, (r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),k1_xboole_0)|r2_hidden(esk1_3(X1,k1_xboole_0,k1_xboole_0),X1)|~r2_hidden(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_68]), c_0_79])).
% 1.31/1.48  cnf(c_0_82, negated_conjecture, (r2_hidden(esk1_3(esk7_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)|r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_68, c_0_80])).
% 1.31/1.48  cnf(c_0_83, negated_conjecture, (r2_hidden(esk1_3(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 1.31/1.48  cnf(c_0_84, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_83]), c_0_83])]), ['proof']).
% 1.31/1.48  # SZS output end CNFRefutation
% 1.31/1.48  # Proof object total steps             : 85
% 1.31/1.48  # Proof object clause steps            : 68
% 1.31/1.48  # Proof object formula steps           : 17
% 1.31/1.48  # Proof object conjectures             : 39
% 1.31/1.48  # Proof object clause conjectures      : 36
% 1.31/1.48  # Proof object formula conjectures     : 3
% 1.31/1.48  # Proof object initial clauses used    : 15
% 1.31/1.48  # Proof object initial formulas used   : 8
% 1.31/1.48  # Proof object generating inferences   : 46
% 1.31/1.48  # Proof object simplifying inferences  : 33
% 1.31/1.48  # Training examples: 0 positive, 0 negative
% 1.31/1.48  # Parsed axioms                        : 8
% 1.31/1.48  # Removed by relevancy pruning/SinE    : 0
% 1.31/1.48  # Initial clauses                      : 22
% 1.31/1.48  # Removed in clause preprocessing      : 1
% 1.31/1.48  # Initial clauses in saturation        : 21
% 1.31/1.48  # Processed clauses                    : 2296
% 1.31/1.48  # ...of these trivial                  : 9
% 1.31/1.48  # ...subsumed                          : 1483
% 1.31/1.48  # ...remaining for further processing  : 804
% 1.31/1.48  # Other redundant clauses eliminated   : 4004
% 1.31/1.48  # Clauses deleted for lack of memory   : 0
% 1.31/1.48  # Backward-subsumed                    : 212
% 1.31/1.48  # Backward-rewritten                   : 88
% 1.31/1.48  # Generated clauses                    : 116947
% 1.31/1.48  # ...of the previous two non-trivial   : 111226
% 1.31/1.48  # Contextual simplify-reflections      : 47
% 1.31/1.48  # Paramodulations                      : 112829
% 1.31/1.48  # Factorizations                       : 114
% 1.31/1.48  # Equation resolutions                 : 4005
% 1.31/1.48  # Propositional unsat checks           : 0
% 1.31/1.48  #    Propositional check models        : 0
% 1.31/1.48  #    Propositional check unsatisfiable : 0
% 1.31/1.48  #    Propositional clauses             : 0
% 1.31/1.48  #    Propositional clauses after purity: 0
% 1.31/1.48  #    Propositional unsat core size     : 0
% 1.31/1.48  #    Propositional preprocessing time  : 0.000
% 1.31/1.48  #    Propositional encoding time       : 0.000
% 1.31/1.48  #    Propositional solver time         : 0.000
% 1.31/1.48  #    Success case prop preproc time    : 0.000
% 1.31/1.48  #    Success case prop encoding time   : 0.000
% 1.31/1.48  #    Success case prop solver time     : 0.000
% 1.31/1.48  # Current number of processed clauses  : 476
% 1.31/1.48  #    Positive orientable unit clauses  : 15
% 1.31/1.48  #    Positive unorientable unit clauses: 2
% 1.31/1.48  #    Negative unit clauses             : 12
% 1.31/1.48  #    Non-unit-clauses                  : 447
% 1.31/1.48  # Current number of unprocessed clauses: 108633
% 1.31/1.48  # ...number of literals in the above   : 780143
% 1.31/1.48  # Current number of archived formulas  : 0
% 1.31/1.48  # Current number of archived clauses   : 322
% 1.31/1.48  # Clause-clause subsumption calls (NU) : 67662
% 1.31/1.48  # Rec. Clause-clause subsumption calls : 18034
% 1.31/1.48  # Non-unit clause-clause subsumptions  : 1710
% 1.31/1.48  # Unit Clause-clause subsumption calls : 774
% 1.31/1.48  # Rewrite failures with RHS unbound    : 0
% 1.31/1.48  # BW rewrite match attempts            : 46
% 1.31/1.48  # BW rewrite match successes           : 20
% 1.31/1.48  # Condensation attempts                : 0
% 1.31/1.48  # Condensation successes               : 0
% 1.31/1.48  # Termbank termtop insertions          : 3038017
% 1.31/1.49  
% 1.31/1.49  # -------------------------------------------------
% 1.31/1.49  # User time                : 1.100 s
% 1.31/1.49  # System time              : 0.046 s
% 1.31/1.49  # Total time               : 1.146 s
% 1.31/1.49  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
