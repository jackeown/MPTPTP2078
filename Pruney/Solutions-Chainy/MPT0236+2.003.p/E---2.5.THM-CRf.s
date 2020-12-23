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
% DateTime   : Thu Dec  3 10:39:18 EST 2020

% Result     : Theorem 0.71s
% Output     : CNFRefutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   34 (  87 expanded)
%              Number of clauses        :   23 (  44 expanded)
%              Number of leaves         :    5 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  108 ( 458 expanded)
%              Number of equality atoms :   63 ( 225 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(t31_zfmisc_1,conjecture,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(t76_enumset1,axiom,(
    ! [X1] : k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(c_0_5,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | X8 = X5
        | X8 = X6
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X5
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X6
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( esk1_3(X10,X11,X12) != X10
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( esk1_3(X10,X11,X12) != X11
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | esk1_3(X10,X11,X12) = X10
        | esk1_3(X10,X11,X12) = X11
        | X12 = k2_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_6,plain,(
    ! [X17,X18] : k1_enumset1(X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_7,plain,(
    ! [X20,X21,X22,X24,X25,X26,X27,X29] :
      ( ( r2_hidden(X22,esk2_3(X20,X21,X22))
        | ~ r2_hidden(X22,X21)
        | X21 != k3_tarski(X20) )
      & ( r2_hidden(esk2_3(X20,X21,X22),X20)
        | ~ r2_hidden(X22,X21)
        | X21 != k3_tarski(X20) )
      & ( ~ r2_hidden(X24,X25)
        | ~ r2_hidden(X25,X20)
        | r2_hidden(X24,X21)
        | X21 != k3_tarski(X20) )
      & ( ~ r2_hidden(esk3_2(X26,X27),X27)
        | ~ r2_hidden(esk3_2(X26,X27),X29)
        | ~ r2_hidden(X29,X26)
        | X27 = k3_tarski(X26) )
      & ( r2_hidden(esk3_2(X26,X27),esk4_2(X26,X27))
        | r2_hidden(esk3_2(X26,X27),X27)
        | X27 = k3_tarski(X26) )
      & ( r2_hidden(esk4_2(X26,X27),X26)
        | r2_hidden(esk3_2(X26,X27),X27)
        | X27 = k3_tarski(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( X2 = k3_tarski(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_hidden(esk3_2(X1,X2),X3)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X4,X2) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_14,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k1_enumset1(X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_10,c_0_9])).

cnf(c_0_15,plain,
    ( X1 = k3_tarski(X2)
    | r2_hidden(esk4_2(X2,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_13])])).

cnf(c_0_17,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k1_enumset1(X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = X2
    | r2_hidden(esk4_2(k1_enumset1(X1,X1,X2),X2),k1_enumset1(X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t31_zfmisc_1])).

cnf(c_0_20,plain,
    ( esk4_2(k1_enumset1(X1,X1,X2),X2) = X2
    | esk4_2(k1_enumset1(X1,X1,X2),X2) = X1
    | k3_tarski(k1_enumset1(X1,X1,X2)) = X2 ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_22,negated_conjecture,(
    k3_tarski(k1_tarski(esk5_0)) != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_23,plain,(
    ! [X19] : k1_enumset1(X19,X19,X19) = k1_tarski(X19) ),
    inference(variable_rename,[status(thm)],[t76_enumset1])).

cnf(c_0_24,plain,
    ( r2_hidden(esk3_2(X1,X2),esk4_2(X1,X2))
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,plain,
    ( esk4_2(k1_enumset1(X1,X1,X1),X1) = X1
    | k3_tarski(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_20])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X4) ),
    inference(rw,[status(thm)],[c_0_21,c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( k3_tarski(k1_tarski(esk5_0)) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X1)) = X1
    | r2_hidden(esk3_2(k1_enumset1(X1,X1,X1),X1),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_26])])).

cnf(c_0_31,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk5_0,esk5_0,esk5_0)) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_29]),c_0_30])]),c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:29:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.71/0.87  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.71/0.87  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.71/0.87  #
% 0.71/0.87  # Preprocessing time       : 0.027 s
% 0.71/0.87  # Presaturation interreduction done
% 0.71/0.87  
% 0.71/0.87  # Proof found!
% 0.71/0.87  # SZS status Theorem
% 0.71/0.87  # SZS output start CNFRefutation
% 0.71/0.87  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.71/0.87  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.71/0.87  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 0.71/0.87  fof(t31_zfmisc_1, conjecture, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 0.71/0.87  fof(t76_enumset1, axiom, ![X1]:k1_enumset1(X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 0.71/0.87  fof(c_0_5, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(X8=X5|X8=X6)|X7!=k2_tarski(X5,X6))&((X9!=X5|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))&(X9!=X6|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))))&(((esk1_3(X10,X11,X12)!=X10|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11))&(esk1_3(X10,X11,X12)!=X11|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(esk1_3(X10,X11,X12)=X10|esk1_3(X10,X11,X12)=X11)|X12=k2_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.71/0.87  fof(c_0_6, plain, ![X17, X18]:k1_enumset1(X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.71/0.87  fof(c_0_7, plain, ![X20, X21, X22, X24, X25, X26, X27, X29]:((((r2_hidden(X22,esk2_3(X20,X21,X22))|~r2_hidden(X22,X21)|X21!=k3_tarski(X20))&(r2_hidden(esk2_3(X20,X21,X22),X20)|~r2_hidden(X22,X21)|X21!=k3_tarski(X20)))&(~r2_hidden(X24,X25)|~r2_hidden(X25,X20)|r2_hidden(X24,X21)|X21!=k3_tarski(X20)))&((~r2_hidden(esk3_2(X26,X27),X27)|(~r2_hidden(esk3_2(X26,X27),X29)|~r2_hidden(X29,X26))|X27=k3_tarski(X26))&((r2_hidden(esk3_2(X26,X27),esk4_2(X26,X27))|r2_hidden(esk3_2(X26,X27),X27)|X27=k3_tarski(X26))&(r2_hidden(esk4_2(X26,X27),X26)|r2_hidden(esk3_2(X26,X27),X27)|X27=k3_tarski(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.71/0.87  cnf(c_0_8, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.71/0.87  cnf(c_0_9, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.71/0.87  cnf(c_0_10, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.71/0.87  cnf(c_0_11, plain, (X2=k3_tarski(X1)|~r2_hidden(esk3_2(X1,X2),X2)|~r2_hidden(esk3_2(X1,X2),X3)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.71/0.87  cnf(c_0_12, plain, (r2_hidden(esk4_2(X1,X2),X1)|r2_hidden(esk3_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.71/0.87  cnf(c_0_13, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X4,X2)), inference(rw,[status(thm)],[c_0_8, c_0_9])).
% 0.71/0.87  cnf(c_0_14, plain, (X1=X4|X1=X3|X2!=k1_enumset1(X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_10, c_0_9])).
% 0.71/0.87  cnf(c_0_15, plain, (X1=k3_tarski(X2)|r2_hidden(esk4_2(X2,X1),X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_12])).
% 0.71/0.87  cnf(c_0_16, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_13])])).
% 0.71/0.87  cnf(c_0_17, plain, (X1=X2|X1=X3|~r2_hidden(X1,k1_enumset1(X3,X3,X2))), inference(er,[status(thm)],[c_0_14])).
% 0.71/0.87  cnf(c_0_18, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=X2|r2_hidden(esk4_2(k1_enumset1(X1,X1,X2),X2),k1_enumset1(X1,X1,X2))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.71/0.87  fof(c_0_19, negated_conjecture, ~(![X1]:k3_tarski(k1_tarski(X1))=X1), inference(assume_negation,[status(cth)],[t31_zfmisc_1])).
% 0.71/0.87  cnf(c_0_20, plain, (esk4_2(k1_enumset1(X1,X1,X2),X2)=X2|esk4_2(k1_enumset1(X1,X1,X2),X2)=X1|k3_tarski(k1_enumset1(X1,X1,X2))=X2), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.71/0.87  cnf(c_0_21, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.71/0.87  fof(c_0_22, negated_conjecture, k3_tarski(k1_tarski(esk5_0))!=esk5_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.71/0.87  fof(c_0_23, plain, ![X19]:k1_enumset1(X19,X19,X19)=k1_tarski(X19), inference(variable_rename,[status(thm)],[t76_enumset1])).
% 0.71/0.87  cnf(c_0_24, plain, (r2_hidden(esk3_2(X1,X2),esk4_2(X1,X2))|r2_hidden(esk3_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.71/0.87  cnf(c_0_25, plain, (esk4_2(k1_enumset1(X1,X1,X1),X1)=X1|k3_tarski(k1_enumset1(X1,X1,X1))=X1), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_20])])).
% 0.71/0.87  cnf(c_0_26, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X4)), inference(rw,[status(thm)],[c_0_21, c_0_9])).
% 0.71/0.87  cnf(c_0_27, negated_conjecture, (k3_tarski(k1_tarski(esk5_0))!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.71/0.87  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.71/0.87  cnf(c_0_29, plain, (k3_tarski(k1_enumset1(X1,X1,X1))=X1|r2_hidden(esk3_2(k1_enumset1(X1,X1,X1),X1),X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.71/0.87  cnf(c_0_30, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_26])])).
% 0.71/0.87  cnf(c_0_31, negated_conjecture, (k3_tarski(k1_enumset1(esk5_0,esk5_0,esk5_0))!=esk5_0), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.71/0.87  cnf(c_0_32, plain, (k3_tarski(k1_enumset1(X1,X1,X1))=X1), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_29]), c_0_30])]), c_0_29])).
% 0.71/0.87  cnf(c_0_33, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32])]), ['proof']).
% 0.71/0.87  # SZS output end CNFRefutation
% 0.71/0.87  # Proof object total steps             : 34
% 0.71/0.87  # Proof object clause steps            : 23
% 0.71/0.87  # Proof object formula steps           : 11
% 0.71/0.87  # Proof object conjectures             : 6
% 0.71/0.87  # Proof object clause conjectures      : 3
% 0.71/0.87  # Proof object formula conjectures     : 3
% 0.71/0.87  # Proof object initial clauses used    : 9
% 0.71/0.87  # Proof object initial formulas used   : 5
% 0.71/0.87  # Proof object generating inferences   : 6
% 0.71/0.87  # Proof object simplifying inferences  : 16
% 0.71/0.87  # Training examples: 0 positive, 0 negative
% 0.71/0.87  # Parsed axioms                        : 6
% 0.71/0.87  # Removed by relevancy pruning/SinE    : 0
% 0.71/0.87  # Initial clauses                      : 16
% 0.71/0.87  # Removed in clause preprocessing      : 2
% 0.71/0.87  # Initial clauses in saturation        : 14
% 0.71/0.87  # Processed clauses                    : 566
% 0.71/0.87  # ...of these trivial                  : 0
% 0.71/0.87  # ...subsumed                          : 36
% 0.71/0.87  # ...remaining for further processing  : 530
% 0.71/0.87  # Other redundant clauses eliminated   : 110
% 0.71/0.87  # Clauses deleted for lack of memory   : 0
% 0.71/0.87  # Backward-subsumed                    : 0
% 0.71/0.87  # Backward-rewritten                   : 9
% 0.71/0.87  # Generated clauses                    : 25044
% 0.71/0.87  # ...of the previous two non-trivial   : 24538
% 0.71/0.87  # Contextual simplify-reflections      : 4
% 0.71/0.87  # Paramodulations                      : 24910
% 0.71/0.87  # Factorizations                       : 26
% 0.71/0.87  # Equation resolutions                 : 110
% 0.71/0.87  # Propositional unsat checks           : 0
% 0.71/0.87  #    Propositional check models        : 0
% 0.71/0.87  #    Propositional check unsatisfiable : 0
% 0.71/0.87  #    Propositional clauses             : 0
% 0.71/0.87  #    Propositional clauses after purity: 0
% 0.71/0.87  #    Propositional unsat core size     : 0
% 0.71/0.87  #    Propositional preprocessing time  : 0.000
% 0.71/0.87  #    Propositional encoding time       : 0.000
% 0.71/0.87  #    Propositional solver time         : 0.000
% 0.71/0.87  #    Success case prop preproc time    : 0.000
% 0.71/0.87  #    Success case prop encoding time   : 0.000
% 0.71/0.87  #    Success case prop solver time     : 0.000
% 0.71/0.87  # Current number of processed clauses  : 501
% 0.71/0.87  #    Positive orientable unit clauses  : 12
% 0.71/0.87  #    Positive unorientable unit clauses: 0
% 0.71/0.87  #    Negative unit clauses             : 0
% 0.71/0.87  #    Non-unit-clauses                  : 489
% 0.71/0.87  # Current number of unprocessed clauses: 23994
% 0.71/0.87  # ...number of literals in the above   : 171876
% 0.71/0.87  # Current number of archived formulas  : 0
% 0.71/0.87  # Current number of archived clauses   : 25
% 0.71/0.87  # Clause-clause subsumption calls (NU) : 39033
% 0.71/0.87  # Rec. Clause-clause subsumption calls : 15488
% 0.71/0.87  # Non-unit clause-clause subsumptions  : 40
% 0.71/0.87  # Unit Clause-clause subsumption calls : 589
% 0.71/0.87  # Rewrite failures with RHS unbound    : 0
% 0.71/0.87  # BW rewrite match attempts            : 1088
% 0.71/0.87  # BW rewrite match successes           : 2
% 0.71/0.87  # Condensation attempts                : 0
% 0.71/0.87  # Condensation successes               : 0
% 0.71/0.87  # Termbank termtop insertions          : 887231
% 0.71/0.87  
% 0.71/0.87  # -------------------------------------------------
% 0.71/0.87  # User time                : 0.520 s
% 0.71/0.87  # System time              : 0.017 s
% 0.71/0.87  # Total time               : 0.537 s
% 0.71/0.87  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
