%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:47 EST 2020

% Result     : Theorem 18.98s
% Output     : CNFRefutation 18.98s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 545 expanded)
%              Number of clauses        :   54 ( 225 expanded)
%              Number of leaves         :   12 ( 154 expanded)
%              Depth                    :   13
%              Number of atoms          :  182 (1208 expanded)
%              Number of equality atoms :   78 ( 656 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t148_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & k3_xboole_0(X2,X3) = k1_tarski(X4)
        & r2_hidden(X4,X1) )
     => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(t60_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,X2)
     => ( ( r2_hidden(X3,X2)
          & X1 != X3 )
        | k3_xboole_0(k2_tarski(X1,X3),X2) = k1_tarski(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(c_0_12,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( r2_hidden(X11,X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X8)
        | ~ r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X13)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X14)
        | X15 = k3_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k3_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X14)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k3_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_13,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k4_xboole_0(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_14,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(X17,X18)
      | k3_xboole_0(X17,X18) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & k3_xboole_0(X2,X3) = k1_tarski(X4)
          & r2_hidden(X4,X1) )
       => k3_xboole_0(X1,X3) = k1_tarski(X4) ) ),
    inference(assume_negation,[status(cth)],[t148_zfmisc_1])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0)
    & k3_xboole_0(esk3_0,esk4_0) = k1_tarski(esk5_0)
    & r2_hidden(esk5_0,esk2_0)
    & k3_xboole_0(esk2_0,esk4_0) != k1_tarski(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_20,plain,(
    ! [X49,X50,X51] :
      ( ( r2_hidden(X51,X50)
        | k3_xboole_0(k2_tarski(X49,X51),X50) = k1_tarski(X49)
        | ~ r2_hidden(X49,X50) )
      & ( X49 != X51
        | k3_xboole_0(k2_tarski(X49,X51),X50) = k1_tarski(X49)
        | ~ r2_hidden(X49,X50) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_zfmisc_1])])])).

fof(c_0_21,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X27,X28,X29,X30] : k3_enumset1(X27,X27,X28,X29,X30) = k2_enumset1(X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,plain,(
    ! [X31,X32,X33,X34,X35] : k4_enumset1(X31,X31,X32,X33,X34,X35) = k3_enumset1(X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_26,plain,(
    ! [X36,X37,X38,X39,X40,X41] : k5_enumset1(X36,X36,X37,X38,X39,X40,X41) = k4_enumset1(X36,X37,X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_27,plain,(
    ! [X42,X43,X44,X45,X46,X47,X48] : k6_enumset1(X42,X42,X43,X44,X45,X46,X47,X48) = k5_enumset1(X42,X43,X44,X45,X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X4,k4_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( k3_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    | X1 != X2
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X4)
    | X4 != k4_xboole_0(X2,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_17])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_44,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | X1 != X2
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_17]),c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_17])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_44,c_0_17])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)) = k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_33]),c_0_34]),c_0_35]),c_0_17]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_52,plain,
    ( k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk5_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_54,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_55,plain,
    ( X1 = k4_xboole_0(X2,k4_xboole_0(X2,X3))
    | r2_hidden(esk1_3(X2,X3,X1),k4_xboole_0(X3,k4_xboole_0(X3,X4)))
    | r2_hidden(esk1_3(X2,X3,X1),X1)
    | ~ r2_hidden(esk1_3(X2,X3,X1),X4) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( X1 = k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X2))
    | r2_hidden(esk1_3(esk2_0,X2,X1),esk3_0)
    | r2_hidden(esk1_3(esk2_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk2_0)) = k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_54,c_0_17])).

cnf(c_0_60,negated_conjecture,
    ( X1 = k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X2))
    | r2_hidden(esk1_3(esk2_0,X2,X1),k4_xboole_0(X2,k4_xboole_0(X2,esk3_0)))
    | r2_hidden(esk1_3(esk2_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | r2_hidden(esk1_3(X1,X2,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),esk4_0)
    | r2_hidden(esk1_3(X1,X2,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_48])).

cnf(c_0_62,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_58])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_65,negated_conjecture,
    ( X1 = k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X2))
    | r2_hidden(esk1_3(esk2_0,X2,X1),k4_xboole_0(X2,k4_xboole_0(X2,esk3_0)))
    | ~ r2_hidden(esk1_3(esk2_0,X2,X1),esk2_0)
    | ~ r2_hidden(esk1_3(esk2_0,X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,esk4_0)) = k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | r2_hidden(esk1_3(X1,esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),esk4_0) ),
    inference(ef,[status(thm)],[c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0)) != k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_33]),c_0_34]),c_0_35]),c_0_17]),c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_68,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | r2_hidden(esk1_3(X1,X2,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),esk2_0)
    | r2_hidden(esk1_3(X1,X2,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_50])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X2,k4_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_64,c_0_17])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))
    | ~ r2_hidden(esk1_3(esk2_0,esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X1)) = k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | r2_hidden(esk1_3(esk2_0,X1,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),esk2_0) ),
    inference(ef,[status(thm)],[c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( X1 = k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X2))
    | r2_hidden(esk1_3(esk2_0,X2,X1),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X3)))
    | r2_hidden(esk1_3(esk2_0,X2,X1),X1)
    | ~ r2_hidden(esk1_3(esk2_0,X2,X1),X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_56])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_66]),c_0_51])]),c_0_67])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_hidden(esk1_3(esk2_0,esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_75]),c_0_76])]),c_0_67])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_71]),c_0_67]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:40:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 18.98/19.21  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S002I
% 18.98/19.21  # and selection function SelectNegativeLiterals.
% 18.98/19.21  #
% 18.98/19.21  # Preprocessing time       : 0.027 s
% 18.98/19.21  # Presaturation interreduction done
% 18.98/19.21  
% 18.98/19.21  # Proof found!
% 18.98/19.21  # SZS status Theorem
% 18.98/19.21  # SZS output start CNFRefutation
% 18.98/19.21  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 18.98/19.21  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 18.98/19.21  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 18.98/19.21  fof(t148_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 18.98/19.21  fof(t60_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,X2)=>((r2_hidden(X3,X2)&X1!=X3)|k3_xboole_0(k2_tarski(X1,X3),X2)=k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_zfmisc_1)).
% 18.98/19.21  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 18.98/19.21  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 18.98/19.21  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 18.98/19.21  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 18.98/19.21  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 18.98/19.21  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 18.98/19.21  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 18.98/19.21  fof(c_0_12, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:((((r2_hidden(X11,X8)|~r2_hidden(X11,X10)|X10!=k3_xboole_0(X8,X9))&(r2_hidden(X11,X9)|~r2_hidden(X11,X10)|X10!=k3_xboole_0(X8,X9)))&(~r2_hidden(X12,X8)|~r2_hidden(X12,X9)|r2_hidden(X12,X10)|X10!=k3_xboole_0(X8,X9)))&((~r2_hidden(esk1_3(X13,X14,X15),X15)|(~r2_hidden(esk1_3(X13,X14,X15),X13)|~r2_hidden(esk1_3(X13,X14,X15),X14))|X15=k3_xboole_0(X13,X14))&((r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k3_xboole_0(X13,X14))&(r2_hidden(esk1_3(X13,X14,X15),X14)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k3_xboole_0(X13,X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 18.98/19.21  fof(c_0_13, plain, ![X19, X20]:k4_xboole_0(X19,k4_xboole_0(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 18.98/19.21  fof(c_0_14, plain, ![X17, X18]:(~r1_tarski(X17,X18)|k3_xboole_0(X17,X18)=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 18.98/19.21  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&k3_xboole_0(X2,X3)=k1_tarski(X4))&r2_hidden(X4,X1))=>k3_xboole_0(X1,X3)=k1_tarski(X4))), inference(assume_negation,[status(cth)],[t148_zfmisc_1])).
% 18.98/19.21  cnf(c_0_16, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 18.98/19.21  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 18.98/19.21  cnf(c_0_18, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 18.98/19.21  fof(c_0_19, negated_conjecture, (((r1_tarski(esk2_0,esk3_0)&k3_xboole_0(esk3_0,esk4_0)=k1_tarski(esk5_0))&r2_hidden(esk5_0,esk2_0))&k3_xboole_0(esk2_0,esk4_0)!=k1_tarski(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 18.98/19.21  fof(c_0_20, plain, ![X49, X50, X51]:((r2_hidden(X51,X50)|k3_xboole_0(k2_tarski(X49,X51),X50)=k1_tarski(X49)|~r2_hidden(X49,X50))&(X49!=X51|k3_xboole_0(k2_tarski(X49,X51),X50)=k1_tarski(X49)|~r2_hidden(X49,X50))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_zfmisc_1])])])).
% 18.98/19.21  fof(c_0_21, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 18.98/19.21  fof(c_0_22, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 18.98/19.21  fof(c_0_23, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 18.98/19.21  fof(c_0_24, plain, ![X27, X28, X29, X30]:k3_enumset1(X27,X27,X28,X29,X30)=k2_enumset1(X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 18.98/19.21  fof(c_0_25, plain, ![X31, X32, X33, X34, X35]:k4_enumset1(X31,X31,X32,X33,X34,X35)=k3_enumset1(X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 18.98/19.21  fof(c_0_26, plain, ![X36, X37, X38, X39, X40, X41]:k5_enumset1(X36,X36,X37,X38,X39,X40,X41)=k4_enumset1(X36,X37,X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 18.98/19.21  fof(c_0_27, plain, ![X42, X43, X44, X45, X46, X47, X48]:k6_enumset1(X42,X42,X43,X44,X45,X46,X47,X48)=k5_enumset1(X42,X43,X44,X45,X46,X47,X48), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 18.98/19.21  cnf(c_0_28, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 18.98/19.21  cnf(c_0_29, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X4,k4_xboole_0(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 18.98/19.21  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_18, c_0_17])).
% 18.98/19.21  cnf(c_0_31, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 18.98/19.21  cnf(c_0_32, plain, (k3_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)|X1!=X2|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 18.98/19.21  cnf(c_0_33, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 18.98/19.21  cnf(c_0_34, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 18.98/19.21  cnf(c_0_35, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 18.98/19.21  cnf(c_0_36, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 18.98/19.21  cnf(c_0_37, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 18.98/19.21  cnf(c_0_38, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 18.98/19.21  cnf(c_0_39, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 18.98/19.21  cnf(c_0_40, plain, (r2_hidden(X1,X4)|X4!=k4_xboole_0(X2,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_17])).
% 18.98/19.21  cnf(c_0_41, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 18.98/19.21  cnf(c_0_42, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(er,[status(thm)],[c_0_29])).
% 18.98/19.21  cnf(c_0_43, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))=esk2_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 18.98/19.21  cnf(c_0_44, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 18.98/19.21  cnf(c_0_45, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 18.98/19.21  cnf(c_0_46, plain, (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),X3))=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|X1!=X2|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_17]), c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39])).
% 18.98/19.21  cnf(c_0_47, plain, (r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_40])).
% 18.98/19.21  cnf(c_0_48, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_41, c_0_17])).
% 18.98/19.21  cnf(c_0_49, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 18.98/19.21  cnf(c_0_50, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_44, c_0_17])).
% 18.98/19.21  cnf(c_0_51, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_33]), c_0_34]), c_0_35]), c_0_17]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 18.98/19.21  cnf(c_0_52, plain, (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_46])).
% 18.98/19.21  cnf(c_0_53, negated_conjecture, (r2_hidden(esk5_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 18.98/19.21  cnf(c_0_54, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 18.98/19.21  cnf(c_0_55, plain, (X1=k4_xboole_0(X2,k4_xboole_0(X2,X3))|r2_hidden(esk1_3(X2,X3,X1),k4_xboole_0(X3,k4_xboole_0(X3,X4)))|r2_hidden(esk1_3(X2,X3,X1),X1)|~r2_hidden(esk1_3(X2,X3,X1),X4)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 18.98/19.21  cnf(c_0_56, negated_conjecture, (X1=k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X2))|r2_hidden(esk1_3(esk2_0,X2,X1),esk3_0)|r2_hidden(esk1_3(esk2_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 18.98/19.21  cnf(c_0_57, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_42, c_0_51])).
% 18.98/19.21  cnf(c_0_58, negated_conjecture, (k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k4_xboole_0(k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk2_0))=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 18.98/19.21  cnf(c_0_59, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_54, c_0_17])).
% 18.98/19.21  cnf(c_0_60, negated_conjecture, (X1=k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X2))|r2_hidden(esk1_3(esk2_0,X2,X1),k4_xboole_0(X2,k4_xboole_0(X2,esk3_0)))|r2_hidden(esk1_3(esk2_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 18.98/19.21  cnf(c_0_61, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|r2_hidden(esk1_3(X1,X2,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),esk4_0)|r2_hidden(esk1_3(X1,X2,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),X2)), inference(spm,[status(thm)],[c_0_57, c_0_48])).
% 18.98/19.21  cnf(c_0_62, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 18.98/19.21  cnf(c_0_63, negated_conjecture, (r2_hidden(X1,esk2_0)|~r2_hidden(X1,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_42, c_0_58])).
% 18.98/19.21  cnf(c_0_64, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 18.98/19.21  cnf(c_0_65, negated_conjecture, (X1=k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X2))|r2_hidden(esk1_3(esk2_0,X2,X1),k4_xboole_0(X2,k4_xboole_0(X2,esk3_0)))|~r2_hidden(esk1_3(esk2_0,X2,X1),esk2_0)|~r2_hidden(esk1_3(esk2_0,X2,X1),X2)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 18.98/19.21  cnf(c_0_66, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,esk4_0))=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|r2_hidden(esk1_3(X1,esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),esk4_0)), inference(ef,[status(thm)],[c_0_61])).
% 18.98/19.21  cnf(c_0_67, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk4_0))!=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_33]), c_0_34]), c_0_35]), c_0_17]), c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 18.98/19.21  cnf(c_0_68, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|r2_hidden(esk1_3(X1,X2,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),esk2_0)|r2_hidden(esk1_3(X1,X2,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),X1)), inference(spm,[status(thm)],[c_0_63, c_0_50])).
% 18.98/19.21  cnf(c_0_69, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X2,k4_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_64, c_0_17])).
% 18.98/19.21  cnf(c_0_70, negated_conjecture, (r2_hidden(esk1_3(esk2_0,esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))|~r2_hidden(esk1_3(esk2_0,esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])).
% 18.98/19.21  cnf(c_0_71, negated_conjecture, (k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X1))=k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|r2_hidden(esk1_3(esk2_0,X1,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),esk2_0)), inference(ef,[status(thm)],[c_0_68])).
% 18.98/19.21  cnf(c_0_72, negated_conjecture, (X1=k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,X2))|r2_hidden(esk1_3(esk2_0,X2,X1),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X3)))|r2_hidden(esk1_3(esk2_0,X2,X1),X1)|~r2_hidden(esk1_3(esk2_0,X2,X1),X3)), inference(spm,[status(thm)],[c_0_47, c_0_56])).
% 18.98/19.21  cnf(c_0_73, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_69])).
% 18.98/19.21  cnf(c_0_74, negated_conjecture, (r2_hidden(esk1_3(esk2_0,esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_67])).
% 18.98/19.21  cnf(c_0_75, negated_conjecture, (r2_hidden(esk1_3(esk2_0,esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_66]), c_0_51])]), c_0_67])).
% 18.98/19.21  cnf(c_0_76, negated_conjecture, (r2_hidden(esk1_3(esk2_0,esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),esk4_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 18.98/19.21  cnf(c_0_77, negated_conjecture, (~r2_hidden(esk1_3(esk2_0,esk4_0,k6_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_75]), c_0_76])]), c_0_67])).
% 18.98/19.21  cnf(c_0_78, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_71]), c_0_67]), ['proof']).
% 18.98/19.21  # SZS output end CNFRefutation
% 18.98/19.21  # Proof object total steps             : 79
% 18.98/19.21  # Proof object clause steps            : 54
% 18.98/19.21  # Proof object formula steps           : 25
% 18.98/19.21  # Proof object conjectures             : 28
% 18.98/19.21  # Proof object clause conjectures      : 25
% 18.98/19.21  # Proof object formula conjectures     : 3
% 18.98/19.21  # Proof object initial clauses used    : 20
% 18.98/19.21  # Proof object initial formulas used   : 12
% 18.98/19.21  # Proof object generating inferences   : 20
% 18.98/19.21  # Proof object simplifying inferences  : 54
% 18.98/19.21  # Training examples: 0 positive, 0 negative
% 18.98/19.21  # Parsed axioms                        : 12
% 18.98/19.21  # Removed by relevancy pruning/SinE    : 0
% 18.98/19.21  # Initial clauses                      : 21
% 18.98/19.21  # Removed in clause preprocessing      : 8
% 18.98/19.21  # Initial clauses in saturation        : 13
% 18.98/19.21  # Processed clauses                    : 22101
% 18.98/19.21  # ...of these trivial                  : 25
% 18.98/19.21  # ...subsumed                          : 19198
% 18.98/19.21  # ...remaining for further processing  : 2878
% 18.98/19.21  # Other redundant clauses eliminated   : 4
% 18.98/19.21  # Clauses deleted for lack of memory   : 0
% 18.98/19.21  # Backward-subsumed                    : 59
% 18.98/19.21  # Backward-rewritten                   : 62
% 18.98/19.21  # Generated clauses                    : 796388
% 18.98/19.21  # ...of the previous two non-trivial   : 787002
% 18.98/19.21  # Contextual simplify-reflections      : 41
% 18.98/19.21  # Paramodulations                      : 795192
% 18.98/19.21  # Factorizations                       : 1192
% 18.98/19.21  # Equation resolutions                 : 4
% 18.98/19.21  # Propositional unsat checks           : 0
% 18.98/19.21  #    Propositional check models        : 0
% 18.98/19.21  #    Propositional check unsatisfiable : 0
% 18.98/19.21  #    Propositional clauses             : 0
% 18.98/19.21  #    Propositional clauses after purity: 0
% 18.98/19.21  #    Propositional unsat core size     : 0
% 18.98/19.21  #    Propositional preprocessing time  : 0.000
% 18.98/19.21  #    Propositional encoding time       : 0.000
% 18.98/19.21  #    Propositional solver time         : 0.000
% 18.98/19.21  #    Success case prop preproc time    : 0.000
% 18.98/19.21  #    Success case prop encoding time   : 0.000
% 18.98/19.21  #    Success case prop solver time     : 0.000
% 18.98/19.21  # Current number of processed clauses  : 2740
% 18.98/19.21  #    Positive orientable unit clauses  : 76
% 18.98/19.21  #    Positive unorientable unit clauses: 0
% 18.98/19.21  #    Negative unit clauses             : 2
% 18.98/19.21  #    Non-unit-clauses                  : 2662
% 18.98/19.21  # Current number of unprocessed clauses: 764435
% 18.98/19.21  # ...number of literals in the above   : 3411266
% 18.98/19.21  # Current number of archived formulas  : 0
% 18.98/19.21  # Current number of archived clauses   : 142
% 18.98/19.21  # Clause-clause subsumption calls (NU) : 2110559
% 18.98/19.21  # Rec. Clause-clause subsumption calls : 825797
% 18.98/19.21  # Non-unit clause-clause subsumptions  : 19296
% 18.98/19.21  # Unit Clause-clause subsumption calls : 4426
% 18.98/19.21  # Rewrite failures with RHS unbound    : 0
% 18.98/19.21  # BW rewrite match attempts            : 984
% 18.98/19.21  # BW rewrite match successes           : 7
% 18.98/19.21  # Condensation attempts                : 0
% 18.98/19.21  # Condensation successes               : 0
% 18.98/19.21  # Termbank termtop insertions          : 143372038
% 19.06/19.24  
% 19.06/19.24  # -------------------------------------------------
% 19.06/19.24  # User time                : 18.463 s
% 19.06/19.24  # System time              : 0.428 s
% 19.06/19.24  # Total time               : 18.891 s
% 19.06/19.24  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
