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
% DateTime   : Thu Dec  3 10:39:28 EST 2020

% Result     : Theorem 17.25s
% Output     : CNFRefutation 17.25s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 101 expanded)
%              Number of clauses        :   24 (  52 expanded)
%              Number of leaves         :    4 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :  114 ( 394 expanded)
%              Number of equality atoms :   71 ( 241 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

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

fof(t35_zfmisc_1,conjecture,(
    ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(c_0_4,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X9,X8)
        | X9 = X7
        | X8 != k1_tarski(X7) )
      & ( X10 != X7
        | r2_hidden(X10,X8)
        | X8 != k1_tarski(X7) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | esk1_2(X11,X12) != X11
        | X12 = k1_tarski(X11) )
      & ( r2_hidden(esk1_2(X11,X12),X12)
        | esk1_2(X11,X12) = X11
        | X12 = k1_tarski(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_5,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_6,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( X1 = X3
    | X2 != k2_tarski(X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_6,c_0_7])).

fof(c_0_9,plain,(
    ! [X15,X16,X17,X18,X21,X22,X23,X24,X25,X26,X28,X29] :
      ( ( r2_hidden(esk2_4(X15,X16,X17,X18),X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k2_zfmisc_1(X15,X16) )
      & ( r2_hidden(esk3_4(X15,X16,X17,X18),X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k2_zfmisc_1(X15,X16) )
      & ( X18 = k4_tarski(esk2_4(X15,X16,X17,X18),esk3_4(X15,X16,X17,X18))
        | ~ r2_hidden(X18,X17)
        | X17 != k2_zfmisc_1(X15,X16) )
      & ( ~ r2_hidden(X22,X15)
        | ~ r2_hidden(X23,X16)
        | X21 != k4_tarski(X22,X23)
        | r2_hidden(X21,X17)
        | X17 != k2_zfmisc_1(X15,X16) )
      & ( ~ r2_hidden(esk4_3(X24,X25,X26),X26)
        | ~ r2_hidden(X28,X24)
        | ~ r2_hidden(X29,X25)
        | esk4_3(X24,X25,X26) != k4_tarski(X28,X29)
        | X26 = k2_zfmisc_1(X24,X25) )
      & ( r2_hidden(esk5_3(X24,X25,X26),X24)
        | r2_hidden(esk4_3(X24,X25,X26),X26)
        | X26 = k2_zfmisc_1(X24,X25) )
      & ( r2_hidden(esk6_3(X24,X25,X26),X25)
        | r2_hidden(esk4_3(X24,X25,X26),X26)
        | X26 = k2_zfmisc_1(X24,X25) )
      & ( esk4_3(X24,X25,X26) = k4_tarski(esk5_3(X24,X25,X26),esk6_3(X24,X25,X26))
        | r2_hidden(esk4_3(X24,X25,X26),X26)
        | X26 = k2_zfmisc_1(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_10,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( esk4_3(X1,X2,X3) = k4_tarski(esk5_3(X1,X2,X3),esk6_3(X1,X2,X3))
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( esk6_3(X1,k2_tarski(X2,X2),X3) = X2
    | X3 = k2_zfmisc_1(X1,k2_tarski(X2,X2))
    | r2_hidden(esk4_3(X1,k2_tarski(X2,X2),X3),X3) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X1)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k4_tarski(esk5_3(X1,X2,k2_tarski(X3,X3)),esk6_3(X1,X2,k2_tarski(X3,X3))) = esk4_3(X1,X2,k2_tarski(X3,X3))
    | esk4_3(X1,X2,k2_tarski(X3,X3)) = X3
    | k2_tarski(X3,X3) = k2_zfmisc_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_12])).

cnf(c_0_16,plain,
    ( esk6_3(X1,k2_tarski(X2,X2),k2_tarski(X3,X3)) = X2
    | esk4_3(X1,k2_tarski(X2,X2),k2_tarski(X3,X3)) = X3
    | k2_tarski(X3,X3) = k2_zfmisc_1(X1,k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_13])).

cnf(c_0_17,plain,
    ( esk5_3(k2_tarski(X1,X1),X2,X3) = X1
    | X3 = k2_zfmisc_1(k2_tarski(X1,X1),X2)
    | r2_hidden(esk4_3(k2_tarski(X1,X1),X2,X3),X3) ),
    inference(spm,[status(thm)],[c_0_10,c_0_14])).

cnf(c_0_18,plain,
    ( k4_tarski(esk5_3(X1,k2_tarski(X2,X2),k2_tarski(X3,X3)),X2) = esk4_3(X1,k2_tarski(X2,X2),k2_tarski(X3,X3))
    | esk4_3(X1,k2_tarski(X2,X2),k2_tarski(X3,X3)) = X3
    | k2_tarski(X3,X3) = k2_zfmisc_1(X1,k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,plain,
    ( esk5_3(k2_tarski(X1,X1),X2,k2_tarski(X3,X3)) = X1
    | esk4_3(k2_tarski(X1,X1),X2,k2_tarski(X3,X3)) = X3
    | k2_tarski(X3,X3) = k2_zfmisc_1(k2_tarski(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_17])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t35_zfmisc_1])).

cnf(c_0_22,plain,
    ( esk4_3(k2_tarski(X1,X1),k2_tarski(X2,X2),k2_tarski(X3,X3)) = k4_tarski(X1,X2)
    | esk4_3(k2_tarski(X1,X1),k2_tarski(X2,X2),k2_tarski(X3,X3)) = X3
    | k2_tarski(X3,X3) = k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_7])).

fof(c_0_24,negated_conjecture,(
    k2_zfmisc_1(k1_tarski(esk7_0),k1_tarski(esk8_0)) != k1_tarski(k4_tarski(esk7_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_25,plain,
    ( X3 = k2_zfmisc_1(X1,X2)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X3)
    | ~ r2_hidden(X4,X1)
    | ~ r2_hidden(X5,X2)
    | esk4_3(X1,X2,X3) != k4_tarski(X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,plain,
    ( esk4_3(k2_tarski(X1,X1),k2_tarski(X2,X2),k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2))) = k4_tarski(X1,X2)
    | k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_22])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).

cnf(c_0_28,negated_conjecture,
    ( k2_zfmisc_1(k1_tarski(esk7_0),k1_tarski(esk8_0)) != k1_tarski(k4_tarski(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X2))
    | k4_tarski(X1,X2) != k4_tarski(X3,X4)
    | ~ r2_hidden(X4,k2_tarski(X2,X2))
    | ~ r2_hidden(X3,k2_tarski(X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_30,negated_conjecture,
    ( k2_zfmisc_1(k2_tarski(esk7_0,esk7_0),k2_tarski(esk8_0,esk8_0)) != k2_tarski(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_7]),c_0_7]),c_0_7])).

cnf(c_0_31,plain,
    ( k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_29]),c_0_27]),c_0_27])])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 17.25/17.46  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S080I
% 17.25/17.46  # and selection function SelectCQIArNXTEqFirst.
% 17.25/17.46  #
% 17.25/17.46  # Preprocessing time       : 0.027 s
% 17.25/17.46  # Presaturation interreduction done
% 17.25/17.46  
% 17.25/17.46  # Proof found!
% 17.25/17.46  # SZS status Theorem
% 17.25/17.46  # SZS output start CNFRefutation
% 17.25/17.46  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 17.25/17.46  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 17.25/17.46  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 17.25/17.46  fof(t35_zfmisc_1, conjecture, ![X1, X2]:k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 17.25/17.46  fof(c_0_4, plain, ![X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X9,X8)|X9=X7|X8!=k1_tarski(X7))&(X10!=X7|r2_hidden(X10,X8)|X8!=k1_tarski(X7)))&((~r2_hidden(esk1_2(X11,X12),X12)|esk1_2(X11,X12)!=X11|X12=k1_tarski(X11))&(r2_hidden(esk1_2(X11,X12),X12)|esk1_2(X11,X12)=X11|X12=k1_tarski(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 17.25/17.46  fof(c_0_5, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 17.25/17.46  cnf(c_0_6, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 17.25/17.46  cnf(c_0_7, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 17.25/17.46  cnf(c_0_8, plain, (X1=X3|X2!=k2_tarski(X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_6, c_0_7])).
% 17.25/17.46  fof(c_0_9, plain, ![X15, X16, X17, X18, X21, X22, X23, X24, X25, X26, X28, X29]:(((((r2_hidden(esk2_4(X15,X16,X17,X18),X15)|~r2_hidden(X18,X17)|X17!=k2_zfmisc_1(X15,X16))&(r2_hidden(esk3_4(X15,X16,X17,X18),X16)|~r2_hidden(X18,X17)|X17!=k2_zfmisc_1(X15,X16)))&(X18=k4_tarski(esk2_4(X15,X16,X17,X18),esk3_4(X15,X16,X17,X18))|~r2_hidden(X18,X17)|X17!=k2_zfmisc_1(X15,X16)))&(~r2_hidden(X22,X15)|~r2_hidden(X23,X16)|X21!=k4_tarski(X22,X23)|r2_hidden(X21,X17)|X17!=k2_zfmisc_1(X15,X16)))&((~r2_hidden(esk4_3(X24,X25,X26),X26)|(~r2_hidden(X28,X24)|~r2_hidden(X29,X25)|esk4_3(X24,X25,X26)!=k4_tarski(X28,X29))|X26=k2_zfmisc_1(X24,X25))&(((r2_hidden(esk5_3(X24,X25,X26),X24)|r2_hidden(esk4_3(X24,X25,X26),X26)|X26=k2_zfmisc_1(X24,X25))&(r2_hidden(esk6_3(X24,X25,X26),X25)|r2_hidden(esk4_3(X24,X25,X26),X26)|X26=k2_zfmisc_1(X24,X25)))&(esk4_3(X24,X25,X26)=k4_tarski(esk5_3(X24,X25,X26),esk6_3(X24,X25,X26))|r2_hidden(esk4_3(X24,X25,X26),X26)|X26=k2_zfmisc_1(X24,X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 17.25/17.46  cnf(c_0_10, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(er,[status(thm)],[c_0_8])).
% 17.25/17.46  cnf(c_0_11, plain, (r2_hidden(esk6_3(X1,X2,X3),X2)|r2_hidden(esk4_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 17.25/17.46  cnf(c_0_12, plain, (esk4_3(X1,X2,X3)=k4_tarski(esk5_3(X1,X2,X3),esk6_3(X1,X2,X3))|r2_hidden(esk4_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 17.25/17.46  cnf(c_0_13, plain, (esk6_3(X1,k2_tarski(X2,X2),X3)=X2|X3=k2_zfmisc_1(X1,k2_tarski(X2,X2))|r2_hidden(esk4_3(X1,k2_tarski(X2,X2),X3),X3)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 17.25/17.46  cnf(c_0_14, plain, (r2_hidden(esk5_3(X1,X2,X3),X1)|r2_hidden(esk4_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 17.25/17.46  cnf(c_0_15, plain, (k4_tarski(esk5_3(X1,X2,k2_tarski(X3,X3)),esk6_3(X1,X2,k2_tarski(X3,X3)))=esk4_3(X1,X2,k2_tarski(X3,X3))|esk4_3(X1,X2,k2_tarski(X3,X3))=X3|k2_tarski(X3,X3)=k2_zfmisc_1(X1,X2)), inference(spm,[status(thm)],[c_0_10, c_0_12])).
% 17.25/17.46  cnf(c_0_16, plain, (esk6_3(X1,k2_tarski(X2,X2),k2_tarski(X3,X3))=X2|esk4_3(X1,k2_tarski(X2,X2),k2_tarski(X3,X3))=X3|k2_tarski(X3,X3)=k2_zfmisc_1(X1,k2_tarski(X2,X2))), inference(spm,[status(thm)],[c_0_10, c_0_13])).
% 17.25/17.46  cnf(c_0_17, plain, (esk5_3(k2_tarski(X1,X1),X2,X3)=X1|X3=k2_zfmisc_1(k2_tarski(X1,X1),X2)|r2_hidden(esk4_3(k2_tarski(X1,X1),X2,X3),X3)), inference(spm,[status(thm)],[c_0_10, c_0_14])).
% 17.25/17.46  cnf(c_0_18, plain, (k4_tarski(esk5_3(X1,k2_tarski(X2,X2),k2_tarski(X3,X3)),X2)=esk4_3(X1,k2_tarski(X2,X2),k2_tarski(X3,X3))|esk4_3(X1,k2_tarski(X2,X2),k2_tarski(X3,X3))=X3|k2_tarski(X3,X3)=k2_zfmisc_1(X1,k2_tarski(X2,X2))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 17.25/17.46  cnf(c_0_19, plain, (esk5_3(k2_tarski(X1,X1),X2,k2_tarski(X3,X3))=X1|esk4_3(k2_tarski(X1,X1),X2,k2_tarski(X3,X3))=X3|k2_tarski(X3,X3)=k2_zfmisc_1(k2_tarski(X1,X1),X2)), inference(spm,[status(thm)],[c_0_10, c_0_17])).
% 17.25/17.46  cnf(c_0_20, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 17.25/17.46  fof(c_0_21, negated_conjecture, ~(![X1, X2]:k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2))), inference(assume_negation,[status(cth)],[t35_zfmisc_1])).
% 17.25/17.46  cnf(c_0_22, plain, (esk4_3(k2_tarski(X1,X1),k2_tarski(X2,X2),k2_tarski(X3,X3))=k4_tarski(X1,X2)|esk4_3(k2_tarski(X1,X1),k2_tarski(X2,X2),k2_tarski(X3,X3))=X3|k2_tarski(X3,X3)=k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X2))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 17.25/17.46  cnf(c_0_23, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_20, c_0_7])).
% 17.25/17.46  fof(c_0_24, negated_conjecture, k2_zfmisc_1(k1_tarski(esk7_0),k1_tarski(esk8_0))!=k1_tarski(k4_tarski(esk7_0,esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 17.25/17.46  cnf(c_0_25, plain, (X3=k2_zfmisc_1(X1,X2)|~r2_hidden(esk4_3(X1,X2,X3),X3)|~r2_hidden(X4,X1)|~r2_hidden(X5,X2)|esk4_3(X1,X2,X3)!=k4_tarski(X4,X5)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 17.25/17.46  cnf(c_0_26, plain, (esk4_3(k2_tarski(X1,X1),k2_tarski(X2,X2),k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2)))=k4_tarski(X1,X2)|k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2))=k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X2))), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_22])])).
% 17.25/17.46  cnf(c_0_27, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).
% 17.25/17.46  cnf(c_0_28, negated_conjecture, (k2_zfmisc_1(k1_tarski(esk7_0),k1_tarski(esk8_0))!=k1_tarski(k4_tarski(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 17.25/17.46  cnf(c_0_29, plain, (k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2))=k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X2))|k4_tarski(X1,X2)!=k4_tarski(X3,X4)|~r2_hidden(X4,k2_tarski(X2,X2))|~r2_hidden(X3,k2_tarski(X1,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 17.25/17.46  cnf(c_0_30, negated_conjecture, (k2_zfmisc_1(k2_tarski(esk7_0,esk7_0),k2_tarski(esk8_0,esk8_0))!=k2_tarski(k4_tarski(esk7_0,esk8_0),k4_tarski(esk7_0,esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_7]), c_0_7]), c_0_7])).
% 17.25/17.46  cnf(c_0_31, plain, (k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2))=k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_29]), c_0_27]), c_0_27])])).
% 17.25/17.46  cnf(c_0_32, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31])]), ['proof']).
% 17.25/17.46  # SZS output end CNFRefutation
% 17.25/17.46  # Proof object total steps             : 33
% 17.25/17.46  # Proof object clause steps            : 24
% 17.25/17.46  # Proof object formula steps           : 9
% 17.25/17.46  # Proof object conjectures             : 6
% 17.25/17.46  # Proof object clause conjectures      : 3
% 17.25/17.46  # Proof object formula conjectures     : 3
% 17.25/17.46  # Proof object initial clauses used    : 8
% 17.25/17.46  # Proof object initial formulas used   : 4
% 17.25/17.46  # Proof object generating inferences   : 10
% 17.25/17.46  # Proof object simplifying inferences  : 16
% 17.25/17.46  # Training examples: 0 positive, 0 negative
% 17.25/17.46  # Parsed axioms                        : 4
% 17.25/17.46  # Removed by relevancy pruning/SinE    : 0
% 17.25/17.46  # Initial clauses                      : 14
% 17.25/17.46  # Removed in clause preprocessing      : 1
% 17.25/17.46  # Initial clauses in saturation        : 13
% 17.25/17.46  # Processed clauses                    : 4514
% 17.25/17.46  # ...of these trivial                  : 20
% 17.25/17.46  # ...subsumed                          : 2465
% 17.25/17.46  # ...remaining for further processing  : 2029
% 17.25/17.46  # Other redundant clauses eliminated   : 26580
% 17.25/17.46  # Clauses deleted for lack of memory   : 0
% 17.25/17.46  # Backward-subsumed                    : 140
% 17.25/17.46  # Backward-rewritten                   : 673
% 17.25/17.46  # Generated clauses                    : 847029
% 17.25/17.46  # ...of the previous two non-trivial   : 803388
% 17.25/17.46  # Contextual simplify-reflections      : 26
% 17.25/17.46  # Paramodulations                      : 819420
% 17.25/17.46  # Factorizations                       : 872
% 17.25/17.46  # Equation resolutions                 : 26739
% 17.25/17.46  # Propositional unsat checks           : 0
% 17.25/17.46  #    Propositional check models        : 0
% 17.25/17.46  #    Propositional check unsatisfiable : 0
% 17.25/17.46  #    Propositional clauses             : 0
% 17.25/17.46  #    Propositional clauses after purity: 0
% 17.25/17.46  #    Propositional unsat core size     : 0
% 17.25/17.46  #    Propositional preprocessing time  : 0.000
% 17.25/17.46  #    Propositional encoding time       : 0.000
% 17.25/17.46  #    Propositional solver time         : 0.000
% 17.25/17.46  #    Success case prop preproc time    : 0.000
% 17.25/17.46  #    Success case prop encoding time   : 0.000
% 17.25/17.46  #    Success case prop solver time     : 0.000
% 17.25/17.46  # Current number of processed clauses  : 1197
% 17.25/17.46  #    Positive orientable unit clauses  : 6
% 17.25/17.46  #    Positive unorientable unit clauses: 0
% 17.25/17.46  #    Negative unit clauses             : 0
% 17.25/17.46  #    Non-unit-clauses                  : 1191
% 17.25/17.46  # Current number of unprocessed clauses: 798009
% 17.25/17.46  # ...number of literals in the above   : 7656201
% 17.25/17.46  # Current number of archived formulas  : 0
% 17.25/17.46  # Current number of archived clauses   : 827
% 17.25/17.46  # Clause-clause subsumption calls (NU) : 574938
% 17.25/17.46  # Rec. Clause-clause subsumption calls : 108807
% 17.25/17.46  # Non-unit clause-clause subsumptions  : 2549
% 17.25/17.46  # Unit Clause-clause subsumption calls : 974
% 17.25/17.46  # Rewrite failures with RHS unbound    : 0
% 17.25/17.46  # BW rewrite match attempts            : 12
% 17.25/17.46  # BW rewrite match successes           : 8
% 17.25/17.46  # Condensation attempts                : 0
% 17.25/17.46  # Condensation successes               : 0
% 17.25/17.46  # Termbank termtop insertions          : 42224239
% 17.33/17.50  
% 17.33/17.50  # -------------------------------------------------
% 17.33/17.50  # User time                : 16.752 s
% 17.33/17.50  # System time              : 0.406 s
% 17.33/17.50  # Total time               : 17.158 s
% 17.33/17.50  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
