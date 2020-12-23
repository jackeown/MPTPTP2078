%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:00 EST 2020

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 209 expanded)
%              Number of clauses        :   22 (  96 expanded)
%              Number of leaves         :    8 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :   85 ( 392 expanded)
%              Number of equality atoms :   16 (  76 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t20_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & ! [X4] :
            ( ( r1_tarski(X4,X2)
              & r1_tarski(X4,X3) )
           => r1_tarski(X4,X1) ) )
     => X1 = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t31_xboole_1,conjecture,(
    ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(t30_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,k3_xboole_0(X3,X2)) = k3_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_xboole_1)).

fof(t13_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

fof(c_0_8,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,X22)
      | r1_tarski(k2_xboole_0(X21,X23),k2_xboole_0(X22,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).

fof(c_0_9,plain,(
    ! [X5,X6] :
      ( ~ r1_tarski(X5,X6)
      | k2_xboole_0(X5,X6) = X6 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_10,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X15] : r1_tarski(k1_xboole_0,X15) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_13,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( r1_tarski(k2_xboole_0(k1_xboole_0,X1),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_16,plain,(
    ! [X11,X12,X13] :
      ( ( r1_tarski(esk1_3(X11,X12,X13),X12)
        | ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X11,X13)
        | X11 = k3_xboole_0(X12,X13) )
      & ( r1_tarski(esk1_3(X11,X12,X13),X13)
        | ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X11,X13)
        | X11 = k3_xboole_0(X12,X13) )
      & ( ~ r1_tarski(esk1_3(X11,X12,X13),X11)
        | ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X11,X13)
        | X11 = k3_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_xboole_1])])])])).

cnf(c_0_17,plain,
    ( r1_tarski(k2_xboole_0(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_18,plain,
    ( r1_tarski(esk1_3(X1,X2,X3),X3)
    | X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_11]),c_0_14])])).

fof(c_0_20,plain,(
    ! [X19,X20] : r1_tarski(X19,k2_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r1_tarski(esk1_3(X2,X1,X2),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    inference(assume_negation,[status(cth)],[t31_xboole_1])).

fof(c_0_24,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,X17)
      | k2_xboole_0(X16,k3_xboole_0(X18,X17)) = k3_xboole_0(k2_xboole_0(X16,X18),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_xboole_1])])).

cnf(c_0_25,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(esk1_3(X1,X2,X3),X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),X1) = X1
    | r1_tarski(esk1_3(X1,k2_xboole_0(X1,X2),X1),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_27,negated_conjecture,(
    ~ r1_tarski(k2_xboole_0(k3_xboole_0(esk2_0,esk3_0),k3_xboole_0(esk2_0,esk4_0)),k2_xboole_0(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_28,plain,(
    ! [X7,X8,X9,X10] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X9,X10)
      | r1_tarski(k2_xboole_0(X7,X9),k2_xboole_0(X8,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1))
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X3,X2)) = k3_xboole_0(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_19]),c_0_22])])).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k3_xboole_0(esk2_0,esk3_0),k3_xboole_0(esk2_0,esk4_0)),k2_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_14]),c_0_14])])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_19])])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(esk2_0,esk4_0),esk4_0)
    | ~ r1_tarski(k3_xboole_0(esk2_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:51:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 1.49/1.64  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 1.49/1.64  # and selection function PSelectComplexExceptUniqMaxHorn.
% 1.49/1.64  #
% 1.49/1.64  # Preprocessing time       : 0.026 s
% 1.49/1.64  # Presaturation interreduction done
% 1.49/1.64  
% 1.49/1.64  # Proof found!
% 1.49/1.64  # SZS status Theorem
% 1.49/1.64  # SZS output start CNFRefutation
% 1.49/1.64  fof(t9_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_xboole_1)).
% 1.49/1.64  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.49/1.64  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.49/1.64  fof(t20_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&![X4]:((r1_tarski(X4,X2)&r1_tarski(X4,X3))=>r1_tarski(X4,X1)))=>X1=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_xboole_1)).
% 1.49/1.64  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.49/1.64  fof(t31_xboole_1, conjecture, ![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 1.49/1.64  fof(t30_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,k3_xboole_0(X3,X2))=k3_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_xboole_1)).
% 1.49/1.64  fof(t13_xboole_1, axiom, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 1.49/1.64  fof(c_0_8, plain, ![X21, X22, X23]:(~r1_tarski(X21,X22)|r1_tarski(k2_xboole_0(X21,X23),k2_xboole_0(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).
% 1.49/1.64  fof(c_0_9, plain, ![X5, X6]:(~r1_tarski(X5,X6)|k2_xboole_0(X5,X6)=X6), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 1.49/1.64  cnf(c_0_10, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.49/1.64  cnf(c_0_11, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.49/1.64  fof(c_0_12, plain, ![X15]:r1_tarski(k1_xboole_0,X15), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 1.49/1.64  cnf(c_0_13, plain, (r1_tarski(k2_xboole_0(X1,X2),X2)|~r1_tarski(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 1.49/1.64  cnf(c_0_14, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.49/1.64  cnf(c_0_15, plain, (r1_tarski(k2_xboole_0(k1_xboole_0,X1),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 1.49/1.64  fof(c_0_16, plain, ![X11, X12, X13]:(((r1_tarski(esk1_3(X11,X12,X13),X12)|(~r1_tarski(X11,X12)|~r1_tarski(X11,X13))|X11=k3_xboole_0(X12,X13))&(r1_tarski(esk1_3(X11,X12,X13),X13)|(~r1_tarski(X11,X12)|~r1_tarski(X11,X13))|X11=k3_xboole_0(X12,X13)))&(~r1_tarski(esk1_3(X11,X12,X13),X11)|(~r1_tarski(X11,X12)|~r1_tarski(X11,X13))|X11=k3_xboole_0(X12,X13))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_xboole_1])])])])).
% 1.49/1.64  cnf(c_0_17, plain, (r1_tarski(k2_xboole_0(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_15, c_0_14])).
% 1.49/1.64  cnf(c_0_18, plain, (r1_tarski(esk1_3(X1,X2,X3),X3)|X1=k3_xboole_0(X2,X3)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.49/1.64  cnf(c_0_19, plain, (r1_tarski(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_11]), c_0_14])])).
% 1.49/1.64  fof(c_0_20, plain, ![X19, X20]:r1_tarski(X19,k2_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 1.49/1.64  cnf(c_0_21, plain, (k3_xboole_0(X1,X2)=X2|r1_tarski(esk1_3(X2,X1,X2),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 1.49/1.64  cnf(c_0_22, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.49/1.64  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3))), inference(assume_negation,[status(cth)],[t31_xboole_1])).
% 1.49/1.64  fof(c_0_24, plain, ![X16, X17, X18]:(~r1_tarski(X16,X17)|k2_xboole_0(X16,k3_xboole_0(X18,X17))=k3_xboole_0(k2_xboole_0(X16,X18),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_xboole_1])])).
% 1.49/1.64  cnf(c_0_25, plain, (X1=k3_xboole_0(X2,X3)|~r1_tarski(esk1_3(X1,X2,X3),X1)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.49/1.64  cnf(c_0_26, plain, (k3_xboole_0(k2_xboole_0(X1,X2),X1)=X1|r1_tarski(esk1_3(X1,k2_xboole_0(X1,X2),X1),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 1.49/1.64  fof(c_0_27, negated_conjecture, ~r1_tarski(k2_xboole_0(k3_xboole_0(esk2_0,esk3_0),k3_xboole_0(esk2_0,esk4_0)),k2_xboole_0(esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 1.49/1.64  fof(c_0_28, plain, ![X7, X8, X9, X10]:(~r1_tarski(X7,X8)|~r1_tarski(X9,X10)|r1_tarski(k2_xboole_0(X7,X9),k2_xboole_0(X8,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).
% 1.49/1.64  cnf(c_0_29, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))|~r1_tarski(X3,X2)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 1.49/1.64  cnf(c_0_30, plain, (k2_xboole_0(X1,k3_xboole_0(X3,X2))=k3_xboole_0(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.49/1.64  cnf(c_0_31, plain, (k3_xboole_0(k2_xboole_0(X1,X2),X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_19]), c_0_22])])).
% 1.49/1.64  cnf(c_0_32, negated_conjecture, (~r1_tarski(k2_xboole_0(k3_xboole_0(esk2_0,esk3_0),k3_xboole_0(esk2_0,esk4_0)),k2_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.49/1.64  cnf(c_0_33, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.49/1.64  cnf(c_0_34, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_14]), c_0_14])])).
% 1.49/1.64  cnf(c_0_35, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_19])])).
% 1.49/1.64  cnf(c_0_36, negated_conjecture, (~r1_tarski(k3_xboole_0(esk2_0,esk4_0),esk4_0)|~r1_tarski(k3_xboole_0(esk2_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 1.49/1.64  cnf(c_0_37, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 1.49/1.64  cnf(c_0_38, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_37])]), ['proof']).
% 1.49/1.64  # SZS output end CNFRefutation
% 1.49/1.64  # Proof object total steps             : 39
% 1.49/1.64  # Proof object clause steps            : 22
% 1.49/1.64  # Proof object formula steps           : 17
% 1.49/1.64  # Proof object conjectures             : 6
% 1.49/1.64  # Proof object clause conjectures      : 3
% 1.49/1.64  # Proof object formula conjectures     : 3
% 1.49/1.64  # Proof object initial clauses used    : 9
% 1.49/1.64  # Proof object initial formulas used   : 8
% 1.49/1.64  # Proof object generating inferences   : 12
% 1.49/1.64  # Proof object simplifying inferences  : 12
% 1.49/1.64  # Training examples: 0 positive, 0 negative
% 1.49/1.64  # Parsed axioms                        : 8
% 1.49/1.64  # Removed by relevancy pruning/SinE    : 0
% 1.49/1.64  # Initial clauses                      : 10
% 1.49/1.64  # Removed in clause preprocessing      : 0
% 1.49/1.64  # Initial clauses in saturation        : 10
% 1.49/1.64  # Processed clauses                    : 5287
% 1.49/1.64  # ...of these trivial                  : 203
% 1.49/1.64  # ...subsumed                          : 4136
% 1.49/1.64  # ...remaining for further processing  : 948
% 1.49/1.64  # Other redundant clauses eliminated   : 0
% 1.49/1.64  # Clauses deleted for lack of memory   : 0
% 1.49/1.64  # Backward-subsumed                    : 29
% 1.49/1.64  # Backward-rewritten                   : 595
% 1.49/1.64  # Generated clauses                    : 158798
% 1.49/1.64  # ...of the previous two non-trivial   : 144372
% 1.49/1.64  # Contextual simplify-reflections      : 4
% 1.49/1.64  # Paramodulations                      : 158798
% 1.49/1.64  # Factorizations                       : 0
% 1.49/1.64  # Equation resolutions                 : 0
% 1.49/1.64  # Propositional unsat checks           : 0
% 1.49/1.64  #    Propositional check models        : 0
% 1.49/1.64  #    Propositional check unsatisfiable : 0
% 1.49/1.64  #    Propositional clauses             : 0
% 1.49/1.64  #    Propositional clauses after purity: 0
% 1.49/1.64  #    Propositional unsat core size     : 0
% 1.49/1.64  #    Propositional preprocessing time  : 0.000
% 1.49/1.64  #    Propositional encoding time       : 0.000
% 1.49/1.64  #    Propositional solver time         : 0.000
% 1.49/1.64  #    Success case prop preproc time    : 0.000
% 1.49/1.64  #    Success case prop encoding time   : 0.000
% 1.49/1.64  #    Success case prop solver time     : 0.000
% 1.49/1.64  # Current number of processed clauses  : 314
% 1.49/1.64  #    Positive orientable unit clauses  : 31
% 1.49/1.64  #    Positive unorientable unit clauses: 0
% 1.49/1.64  #    Negative unit clauses             : 2
% 1.49/1.64  #    Non-unit-clauses                  : 281
% 1.49/1.64  # Current number of unprocessed clauses: 138655
% 1.49/1.64  # ...number of literals in the above   : 461061
% 1.49/1.64  # Current number of archived formulas  : 0
% 1.49/1.64  # Current number of archived clauses   : 634
% 1.49/1.64  # Clause-clause subsumption calls (NU) : 273927
% 1.49/1.64  # Rec. Clause-clause subsumption calls : 207223
% 1.49/1.64  # Non-unit clause-clause subsumptions  : 4163
% 1.49/1.64  # Unit Clause-clause subsumption calls : 8554
% 1.49/1.64  # Rewrite failures with RHS unbound    : 0
% 1.49/1.64  # BW rewrite match attempts            : 4216
% 1.49/1.64  # BW rewrite match successes           : 74
% 1.49/1.64  # Condensation attempts                : 0
% 1.49/1.64  # Condensation successes               : 0
% 1.49/1.64  # Termbank termtop insertions          : 3423303
% 1.49/1.65  
% 1.49/1.65  # -------------------------------------------------
% 1.49/1.65  # User time                : 1.239 s
% 1.49/1.65  # System time              : 0.078 s
% 1.49/1.65  # Total time               : 1.317 s
% 1.49/1.65  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
