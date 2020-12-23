%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:34 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 938 expanded)
%              Number of clauses        :   49 ( 404 expanded)
%              Number of leaves         :   13 ( 238 expanded)
%              Depth                    :   17
%              Number of atoms          :  148 (1980 expanded)
%              Number of equality atoms :   62 (1154 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( X1 != k1_tarski(X2)
          & X1 != k1_xboole_0
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & X3 != X2 ) ) ),
    inference(assume_negation,[status(cth)],[t41_zfmisc_1])).

fof(c_0_14,negated_conjecture,(
    ! [X43] :
      ( esk4_0 != k1_tarski(esk5_0)
      & esk4_0 != k1_xboole_0
      & ( ~ r2_hidden(X43,esk4_0)
        | X43 = esk5_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).

fof(c_0_15,plain,(
    ! [X22] :
      ( X22 = k1_xboole_0
      | r2_hidden(esk3_1(X22),X22) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_16,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,plain,(
    ! [X37,X38] :
      ( ( ~ r1_tarski(k1_tarski(X37),X38)
        | r2_hidden(X37,X38) )
      & ( ~ r2_hidden(X37,X38)
        | r1_tarski(k1_tarski(X37),X38) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_19,plain,(
    ! [X31] : k2_tarski(X31,X31) = k1_tarski(X31) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,plain,(
    ! [X32,X33] : k1_enumset1(X32,X32,X33) = k2_tarski(X32,X33) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X34,X35,X36] : k2_enumset1(X34,X34,X35,X36) = k1_enumset1(X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_22,negated_conjecture,
    ( X1 = esk5_0
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk3_1(esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( esk3_1(esk4_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_29,plain,(
    ! [X39,X40] :
      ( ~ r1_xboole_0(k1_tarski(X39),X40)
      | ~ r2_hidden(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_30,plain,(
    ! [X29,X30] :
      ( ( ~ r1_xboole_0(X29,X30)
        | k4_xboole_0(X29,X30) = X29 )
      & ( k4_xboole_0(X29,X30) != X29
        | r1_xboole_0(X29,X30) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_31,plain,(
    ! [X26] : k4_xboole_0(X26,k1_xboole_0) = X26 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_32,plain,(
    ! [X24,X25] :
      ( ( k4_xboole_0(X24,X25) != k1_xboole_0
        | r1_tarski(X24,X25) )
      & ( ~ r1_tarski(X24,X25)
        | k4_xboole_0(X24,X25) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_33,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_28])).

cnf(c_0_35,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_40,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k4_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_43,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_44,plain,(
    ! [X27,X28] : k4_xboole_0(X27,k4_xboole_0(X27,X28)) = k3_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_45,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_45]),c_0_45]),c_0_45]),c_0_47])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_49])).

cnf(c_0_54,plain,
    ( r2_hidden(esk3_1(k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X1,X1,X1,X1))
    | ~ r1_xboole_0(k1_xboole_0,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_17])).

cnf(c_0_55,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_50])]),c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( esk4_0 != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) = k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_45]),c_0_37])).

cnf(c_0_60,plain,
    ( r2_hidden(esk3_1(k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X1,X1,X1,X1))
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_61,negated_conjecture,
    ( esk4_0 != k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_37])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk3_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_34])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),k1_xboole_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_50]),c_0_37]),c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(esk3_1(esk4_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_23])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk3_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_68,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_69,negated_conjecture,
    ( esk1_3(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),k1_xboole_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_66,c_0_28])).

cnf(c_0_71,negated_conjecture,
    ( esk3_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( k4_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = k1_xboole_0
    | ~ r2_hidden(esk5_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk5_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( k4_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73])])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_74]),c_0_37]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:33:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.13/0.40  # and selection function SelectNegativeLiterals.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.027 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t41_zfmisc_1, conjecture, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 0.13/0.40  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.13/0.40  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.13/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.40  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.13/0.40  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.13/0.40  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.13/0.40  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.13/0.40  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.13/0.40  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.13/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.40  fof(c_0_13, negated_conjecture, ~(![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2))))), inference(assume_negation,[status(cth)],[t41_zfmisc_1])).
% 0.13/0.40  fof(c_0_14, negated_conjecture, ![X43]:((esk4_0!=k1_tarski(esk5_0)&esk4_0!=k1_xboole_0)&(~r2_hidden(X43,esk4_0)|X43=esk5_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).
% 0.13/0.40  fof(c_0_15, plain, ![X22]:(X22=k1_xboole_0|r2_hidden(esk3_1(X22),X22)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.13/0.40  cnf(c_0_16, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_17, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  fof(c_0_18, plain, ![X37, X38]:((~r1_tarski(k1_tarski(X37),X38)|r2_hidden(X37,X38))&(~r2_hidden(X37,X38)|r1_tarski(k1_tarski(X37),X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.13/0.40  fof(c_0_19, plain, ![X31]:k2_tarski(X31,X31)=k1_tarski(X31), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.40  fof(c_0_20, plain, ![X32, X33]:k1_enumset1(X32,X32,X33)=k2_tarski(X32,X33), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.40  fof(c_0_21, plain, ![X34, X35, X36]:k2_enumset1(X34,X34,X35,X36)=k1_enumset1(X34,X35,X36), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.40  cnf(c_0_22, negated_conjecture, (X1=esk5_0|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_23, negated_conjecture, (r2_hidden(esk3_1(esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.40  cnf(c_0_24, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.40  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.40  cnf(c_0_28, negated_conjecture, (esk3_1(esk4_0)=esk5_0), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.40  fof(c_0_29, plain, ![X39, X40]:(~r1_xboole_0(k1_tarski(X39),X40)|~r2_hidden(X39,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.13/0.40  fof(c_0_30, plain, ![X29, X30]:((~r1_xboole_0(X29,X30)|k4_xboole_0(X29,X30)=X29)&(k4_xboole_0(X29,X30)!=X29|r1_xboole_0(X29,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.13/0.40  fof(c_0_31, plain, ![X26]:k4_xboole_0(X26,k1_xboole_0)=X26, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.13/0.40  fof(c_0_32, plain, ![X24, X25]:((k4_xboole_0(X24,X25)!=k1_xboole_0|r1_tarski(X24,X25))&(~r1_tarski(X24,X25)|k4_xboole_0(X24,X25)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.13/0.40  cnf(c_0_33, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])).
% 0.13/0.40  cnf(c_0_34, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(rw,[status(thm)],[c_0_23, c_0_28])).
% 0.13/0.40  cnf(c_0_35, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.40  cnf(c_0_36, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.40  cnf(c_0_37, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.40  cnf(c_0_38, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.40  cnf(c_0_39, negated_conjecture, (r1_tarski(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.40  fof(c_0_40, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.13/0.40  cnf(c_0_41, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_25]), c_0_26]), c_0_27])).
% 0.13/0.40  cnf(c_0_42, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.40  fof(c_0_43, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.13/0.40  fof(c_0_44, plain, ![X27, X28]:k4_xboole_0(X27,k4_xboole_0(X27,X28))=k3_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.40  cnf(c_0_45, negated_conjecture, (k4_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.40  cnf(c_0_46, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.40  cnf(c_0_47, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.40  cnf(c_0_48, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.40  cnf(c_0_49, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.40  cnf(c_0_50, negated_conjecture, (k4_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk1_3(X1,X2,k1_xboole_0),X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_45]), c_0_45]), c_0_45]), c_0_47])).
% 0.13/0.40  cnf(c_0_51, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.40  cnf(c_0_52, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.40  cnf(c_0_53, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_49])).
% 0.13/0.40  cnf(c_0_54, plain, (r2_hidden(esk3_1(k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X1,X1,X1,X1))|~r1_xboole_0(k1_xboole_0,X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_17])).
% 0.13/0.40  cnf(c_0_55, negated_conjecture, (r1_xboole_0(k1_xboole_0,X1)), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_50])]), c_0_47])).
% 0.13/0.40  cnf(c_0_56, negated_conjecture, (esk4_0!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_57, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_51])).
% 0.13/0.40  cnf(c_0_58, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_52])).
% 0.13/0.40  cnf(c_0_59, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_45]), c_0_37])).
% 0.13/0.40  cnf(c_0_60, plain, (r2_hidden(esk3_1(k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X1,X1,X1,X1))|~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])])).
% 0.13/0.40  cnf(c_0_61, negated_conjecture, (esk4_0!=k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_25]), c_0_26]), c_0_27])).
% 0.13/0.40  cnf(c_0_62, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_57, c_0_37])).
% 0.13/0.40  cnf(c_0_63, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.13/0.40  cnf(c_0_64, negated_conjecture, (r2_hidden(esk3_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_60, c_0_34])).
% 0.13/0.40  cnf(c_0_65, negated_conjecture, (r2_hidden(esk1_3(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),k1_xboole_0),esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_50]), c_0_37]), c_0_61])).
% 0.13/0.40  cnf(c_0_66, negated_conjecture, (~r2_hidden(esk3_1(esk4_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_62, c_0_23])).
% 0.13/0.40  cnf(c_0_67, negated_conjecture, (r2_hidden(esk3_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),esk4_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.13/0.40  cnf(c_0_68, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.40  cnf(c_0_69, negated_conjecture, (esk1_3(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),k1_xboole_0)=esk5_0), inference(spm,[status(thm)],[c_0_22, c_0_65])).
% 0.13/0.40  cnf(c_0_70, negated_conjecture, (~r2_hidden(esk5_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_66, c_0_28])).
% 0.13/0.40  cnf(c_0_71, negated_conjecture, (esk3_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=esk5_0), inference(spm,[status(thm)],[c_0_22, c_0_67])).
% 0.13/0.40  cnf(c_0_72, negated_conjecture, (k4_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=k1_xboole_0|~r2_hidden(esk5_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])).
% 0.13/0.40  cnf(c_0_73, negated_conjecture, (r2_hidden(esk5_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[c_0_64, c_0_71])).
% 0.13/0.40  cnf(c_0_74, negated_conjecture, (k4_xboole_0(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73])])).
% 0.13/0.40  cnf(c_0_75, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_74]), c_0_37]), c_0_61]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 76
% 0.13/0.40  # Proof object clause steps            : 49
% 0.13/0.40  # Proof object formula steps           : 27
% 0.13/0.40  # Proof object conjectures             : 27
% 0.13/0.40  # Proof object clause conjectures      : 24
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 18
% 0.13/0.40  # Proof object initial formulas used   : 13
% 0.13/0.40  # Proof object generating inferences   : 19
% 0.13/0.40  # Proof object simplifying inferences  : 33
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 14
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 26
% 0.13/0.40  # Removed in clause preprocessing      : 4
% 0.13/0.40  # Initial clauses in saturation        : 22
% 0.13/0.40  # Processed clauses                    : 422
% 0.13/0.40  # ...of these trivial                  : 7
% 0.13/0.40  # ...subsumed                          : 273
% 0.13/0.40  # ...remaining for further processing  : 142
% 0.13/0.40  # Other redundant clauses eliminated   : 63
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 4
% 0.13/0.40  # Backward-rewritten                   : 30
% 0.13/0.40  # Generated clauses                    : 1678
% 0.13/0.40  # ...of the previous two non-trivial   : 1344
% 0.13/0.40  # Contextual simplify-reflections      : 1
% 0.13/0.40  # Paramodulations                      : 1615
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 63
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 83
% 0.13/0.40  #    Positive orientable unit clauses  : 17
% 0.13/0.40  #    Positive unorientable unit clauses: 1
% 0.13/0.40  #    Negative unit clauses             : 4
% 0.13/0.40  #    Non-unit-clauses                  : 61
% 0.13/0.40  # Current number of unprocessed clauses: 948
% 0.13/0.40  # ...number of literals in the above   : 2856
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 60
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 1010
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 869
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 148
% 0.13/0.40  # Unit Clause-clause subsumption calls : 347
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 85
% 0.13/0.40  # BW rewrite match successes           : 30
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 20376
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.055 s
% 0.13/0.40  # System time              : 0.006 s
% 0.13/0.40  # Total time               : 0.061 s
% 0.13/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
