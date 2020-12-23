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
% DateTime   : Thu Dec  3 10:43:43 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 165 expanded)
%              Number of clauses        :   29 (  67 expanded)
%              Number of leaves         :    9 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :  115 ( 351 expanded)
%              Number of equality atoms :   58 ( 203 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t128_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))
    <=> ( X1 = X3
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t76_enumset1,axiom,(
    ! [X1] : k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))
      <=> ( X1 = X3
          & r2_hidden(X2,X4) ) ) ),
    inference(assume_negation,[status(cth)],[t128_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X10,X9)
        | X10 = X7
        | X10 = X8
        | X9 != k2_tarski(X7,X8) )
      & ( X11 != X7
        | r2_hidden(X11,X9)
        | X9 != k2_tarski(X7,X8) )
      & ( X11 != X8
        | r2_hidden(X11,X9)
        | X9 != k2_tarski(X7,X8) )
      & ( esk1_3(X12,X13,X14) != X12
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_tarski(X12,X13) )
      & ( esk1_3(X12,X13,X14) != X13
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_tarski(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X14)
        | esk1_3(X12,X13,X14) = X12
        | esk1_3(X12,X13,X14) = X13
        | X14 = k2_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_11,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_13,plain,(
    ! [X21,X22,X23,X24] : k3_enumset1(X21,X21,X22,X23,X24) = k2_enumset1(X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_14,plain,(
    ! [X25,X26,X27,X28,X29] : k4_enumset1(X25,X25,X26,X27,X28,X29) = k3_enumset1(X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_15,plain,(
    ! [X30,X31,X32,X33,X34,X35] : k5_enumset1(X30,X30,X31,X32,X33,X34,X35) = k4_enumset1(X30,X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_16,negated_conjecture,
    ( ( ~ r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),esk5_0))
      | esk2_0 != esk4_0
      | ~ r2_hidden(esk3_0,esk5_0) )
    & ( esk2_0 = esk4_0
      | r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),esk5_0)) )
    & ( r2_hidden(esk3_0,esk5_0)
      | r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),esk5_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_17,plain,(
    ! [X36] : k1_enumset1(X36,X36,X36) = k1_tarski(X36) ),
    inference(variable_rename,[status(thm)],[t76_enumset1])).

cnf(c_0_18,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_24,plain,(
    ! [X37,X38,X39,X40] :
      ( ( r2_hidden(X37,X39)
        | ~ r2_hidden(k4_tarski(X37,X38),k2_zfmisc_1(X39,X40)) )
      & ( r2_hidden(X38,X40)
        | ~ r2_hidden(k4_tarski(X37,X38),k2_zfmisc_1(X39,X40)) )
      & ( ~ r2_hidden(X37,X39)
        | ~ r2_hidden(X38,X40)
        | r2_hidden(k4_tarski(X37,X38),k2_zfmisc_1(X39,X40)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_25,negated_conjecture,
    ( esk2_0 = esk4_0
    | r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),esk5_0))
    | esk2_0 != esk4_0
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k5_enumset1(X3,X3,X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( esk4_0 = esk2_0
    | r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_26]),c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,negated_conjecture,
    ( esk4_0 != esk2_0
    | ~ r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_26]),c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_36,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k5_enumset1(X3,X3,X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( esk2_0 = esk4_0
    | r2_hidden(esk2_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0) ),
    inference(csr,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X4,X4,X4,X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( esk2_0 != esk4_0
    | ~ r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)) ),
    inference(csr,[status(thm)],[c_0_35,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( esk2_0 = esk4_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk3_0),k2_zfmisc_1(X2,esk5_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk4_0,esk3_0),k2_zfmisc_1(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_42])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk3_0),k2_zfmisc_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X1),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:54:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.12/0.40  # and selection function GSelectMinInfpos.
% 0.12/0.40  #
% 0.12/0.40  # Preprocessing time       : 0.043 s
% 0.12/0.40  # Presaturation interreduction done
% 0.12/0.40  
% 0.12/0.40  # Proof found!
% 0.12/0.40  # SZS status Theorem
% 0.12/0.40  # SZS output start CNFRefutation
% 0.12/0.40  fof(t128_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))<=>(X1=X3&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 0.12/0.40  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.12/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.12/0.40  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.12/0.40  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.12/0.40  fof(t76_enumset1, axiom, ![X1]:k1_enumset1(X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 0.12/0.40  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.12/0.40  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))<=>(X1=X3&r2_hidden(X2,X4)))), inference(assume_negation,[status(cth)],[t128_zfmisc_1])).
% 0.12/0.40  fof(c_0_10, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X10,X9)|(X10=X7|X10=X8)|X9!=k2_tarski(X7,X8))&((X11!=X7|r2_hidden(X11,X9)|X9!=k2_tarski(X7,X8))&(X11!=X8|r2_hidden(X11,X9)|X9!=k2_tarski(X7,X8))))&(((esk1_3(X12,X13,X14)!=X12|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_tarski(X12,X13))&(esk1_3(X12,X13,X14)!=X13|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_tarski(X12,X13)))&(r2_hidden(esk1_3(X12,X13,X14),X14)|(esk1_3(X12,X13,X14)=X12|esk1_3(X12,X13,X14)=X13)|X14=k2_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.12/0.40  fof(c_0_11, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.40  fof(c_0_12, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.40  fof(c_0_13, plain, ![X21, X22, X23, X24]:k3_enumset1(X21,X21,X22,X23,X24)=k2_enumset1(X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.12/0.40  fof(c_0_14, plain, ![X25, X26, X27, X28, X29]:k4_enumset1(X25,X25,X26,X27,X28,X29)=k3_enumset1(X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.12/0.40  fof(c_0_15, plain, ![X30, X31, X32, X33, X34, X35]:k5_enumset1(X30,X30,X31,X32,X33,X34,X35)=k4_enumset1(X30,X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.12/0.40  fof(c_0_16, negated_conjecture, ((~r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),esk5_0))|(esk2_0!=esk4_0|~r2_hidden(esk3_0,esk5_0)))&((esk2_0=esk4_0|r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),esk5_0)))&(r2_hidden(esk3_0,esk5_0)|r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),esk5_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.12/0.40  fof(c_0_17, plain, ![X36]:k1_enumset1(X36,X36,X36)=k1_tarski(X36), inference(variable_rename,[status(thm)],[t76_enumset1])).
% 0.12/0.40  cnf(c_0_18, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.40  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.40  cnf(c_0_20, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.40  cnf(c_0_21, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.40  cnf(c_0_22, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.40  cnf(c_0_23, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.40  fof(c_0_24, plain, ![X37, X38, X39, X40]:(((r2_hidden(X37,X39)|~r2_hidden(k4_tarski(X37,X38),k2_zfmisc_1(X39,X40)))&(r2_hidden(X38,X40)|~r2_hidden(k4_tarski(X37,X38),k2_zfmisc_1(X39,X40))))&(~r2_hidden(X37,X39)|~r2_hidden(X38,X40)|r2_hidden(k4_tarski(X37,X38),k2_zfmisc_1(X39,X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.12/0.40  cnf(c_0_25, negated_conjecture, (esk2_0=esk4_0|r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.40  cnf(c_0_26, plain, (k1_enumset1(X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.40  cnf(c_0_27, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.40  cnf(c_0_28, negated_conjecture, (~r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),esk5_0))|esk2_0!=esk4_0|~r2_hidden(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.40  cnf(c_0_29, plain, (X1=X4|X1=X3|X2!=k5_enumset1(X3,X3,X3,X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.12/0.40  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.40  cnf(c_0_31, negated_conjecture, (esk4_0=esk2_0|r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.12/0.40  cnf(c_0_32, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_26]), c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.12/0.40  cnf(c_0_33, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.40  cnf(c_0_34, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.40  cnf(c_0_35, negated_conjecture, (esk4_0!=esk2_0|~r2_hidden(esk3_0,esk5_0)|~r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_26]), c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.12/0.40  cnf(c_0_36, plain, (X1=X2|X1=X3|~r2_hidden(X1,k5_enumset1(X3,X3,X3,X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_29])).
% 0.12/0.40  cnf(c_0_37, negated_conjecture, (esk2_0=esk4_0|r2_hidden(esk2_0,k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.12/0.40  cnf(c_0_38, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.40  cnf(c_0_39, negated_conjecture, (r2_hidden(esk3_0,esk5_0)), inference(csr,[status(thm)],[c_0_32, c_0_33])).
% 0.12/0.40  cnf(c_0_40, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X4,X4,X4,X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23])).
% 0.12/0.40  cnf(c_0_41, negated_conjecture, (esk2_0!=esk4_0|~r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0))), inference(csr,[status(thm)],[c_0_35, c_0_33])).
% 0.12/0.40  cnf(c_0_42, negated_conjecture, (esk2_0=esk4_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.12/0.40  cnf(c_0_43, negated_conjecture, (r2_hidden(k4_tarski(X1,esk3_0),k2_zfmisc_1(X2,esk5_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.12/0.40  cnf(c_0_44, plain, (r2_hidden(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).
% 0.12/0.40  cnf(c_0_45, negated_conjecture, (~r2_hidden(k4_tarski(esk4_0,esk3_0),k2_zfmisc_1(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_42])])).
% 0.12/0.40  cnf(c_0_46, negated_conjecture, (r2_hidden(k4_tarski(X1,esk3_0),k2_zfmisc_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X1),esk5_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.12/0.40  cnf(c_0_47, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46])]), ['proof']).
% 0.12/0.40  # SZS output end CNFRefutation
% 0.12/0.40  # Proof object total steps             : 48
% 0.12/0.40  # Proof object clause steps            : 29
% 0.12/0.40  # Proof object formula steps           : 19
% 0.12/0.40  # Proof object conjectures             : 17
% 0.12/0.40  # Proof object clause conjectures      : 14
% 0.12/0.40  # Proof object formula conjectures     : 3
% 0.12/0.40  # Proof object initial clauses used    : 14
% 0.12/0.40  # Proof object initial formulas used   : 9
% 0.12/0.40  # Proof object generating inferences   : 4
% 0.12/0.40  # Proof object simplifying inferences  : 35
% 0.12/0.40  # Training examples: 0 positive, 0 negative
% 0.12/0.40  # Parsed axioms                        : 9
% 0.12/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.40  # Initial clauses                      : 18
% 0.12/0.40  # Removed in clause preprocessing      : 6
% 0.12/0.40  # Initial clauses in saturation        : 12
% 0.12/0.40  # Processed clauses                    : 61
% 0.12/0.40  # ...of these trivial                  : 0
% 0.12/0.40  # ...subsumed                          : 2
% 0.12/0.40  # ...remaining for further processing  : 59
% 0.12/0.40  # Other redundant clauses eliminated   : 7
% 0.12/0.40  # Clauses deleted for lack of memory   : 0
% 0.12/0.40  # Backward-subsumed                    : 0
% 0.12/0.40  # Backward-rewritten                   : 4
% 0.12/0.40  # Generated clauses                    : 303
% 0.12/0.40  # ...of the previous two non-trivial   : 257
% 0.12/0.40  # Contextual simplify-reflections      : 2
% 0.12/0.40  # Paramodulations                      : 298
% 0.12/0.40  # Factorizations                       : 0
% 0.12/0.40  # Equation resolutions                 : 7
% 0.12/0.40  # Propositional unsat checks           : 0
% 0.12/0.40  #    Propositional check models        : 0
% 0.12/0.40  #    Propositional check unsatisfiable : 0
% 0.12/0.40  #    Propositional clauses             : 0
% 0.12/0.40  #    Propositional clauses after purity: 0
% 0.12/0.40  #    Propositional unsat core size     : 0
% 0.12/0.40  #    Propositional preprocessing time  : 0.000
% 0.12/0.40  #    Propositional encoding time       : 0.000
% 0.12/0.40  #    Propositional solver time         : 0.000
% 0.12/0.40  #    Success case prop preproc time    : 0.000
% 0.12/0.40  #    Success case prop encoding time   : 0.000
% 0.12/0.40  #    Success case prop solver time     : 0.000
% 0.12/0.40  # Current number of processed clauses  : 40
% 0.12/0.40  #    Positive orientable unit clauses  : 17
% 0.12/0.40  #    Positive unorientable unit clauses: 0
% 0.12/0.40  #    Negative unit clauses             : 0
% 0.12/0.40  #    Non-unit-clauses                  : 23
% 0.12/0.40  # Current number of unprocessed clauses: 218
% 0.12/0.40  # ...number of literals in the above   : 943
% 0.12/0.40  # Current number of archived formulas  : 0
% 0.12/0.40  # Current number of archived clauses   : 22
% 0.12/0.40  # Clause-clause subsumption calls (NU) : 262
% 0.12/0.40  # Rec. Clause-clause subsumption calls : 68
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 4
% 0.19/0.40  # Unit Clause-clause subsumption calls : 42
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 24
% 0.19/0.40  # BW rewrite match successes           : 2
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 10191
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.058 s
% 0.19/0.40  # System time              : 0.005 s
% 0.19/0.40  # Total time               : 0.063 s
% 0.19/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
