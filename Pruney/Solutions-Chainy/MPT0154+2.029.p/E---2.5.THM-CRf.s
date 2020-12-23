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
% DateTime   : Thu Dec  3 10:35:34 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 206 expanded)
%              Number of clauses        :   36 ( 111 expanded)
%              Number of leaves         :    3 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  150 (1609 expanded)
%              Number of equality atoms :  116 (1177 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t70_enumset1,conjecture,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(c_0_3,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X10,X9)
        | X10 = X6
        | X10 = X7
        | X10 = X8
        | X9 != k1_enumset1(X6,X7,X8) )
      & ( X11 != X6
        | r2_hidden(X11,X9)
        | X9 != k1_enumset1(X6,X7,X8) )
      & ( X11 != X7
        | r2_hidden(X11,X9)
        | X9 != k1_enumset1(X6,X7,X8) )
      & ( X11 != X8
        | r2_hidden(X11,X9)
        | X9 != k1_enumset1(X6,X7,X8) )
      & ( esk1_4(X12,X13,X14,X15) != X12
        | ~ r2_hidden(esk1_4(X12,X13,X14,X15),X15)
        | X15 = k1_enumset1(X12,X13,X14) )
      & ( esk1_4(X12,X13,X14,X15) != X13
        | ~ r2_hidden(esk1_4(X12,X13,X14,X15),X15)
        | X15 = k1_enumset1(X12,X13,X14) )
      & ( esk1_4(X12,X13,X14,X15) != X14
        | ~ r2_hidden(esk1_4(X12,X13,X14,X15),X15)
        | X15 = k1_enumset1(X12,X13,X14) )
      & ( r2_hidden(esk1_4(X12,X13,X14,X15),X15)
        | esk1_4(X12,X13,X14,X15) = X12
        | esk1_4(X12,X13,X14,X15) = X13
        | esk1_4(X12,X13,X14,X15) = X14
        | X15 = k1_enumset1(X12,X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_4,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_5,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X20,X19)
        | X20 = X17
        | X20 = X18
        | X19 != k2_tarski(X17,X18) )
      & ( X21 != X17
        | r2_hidden(X21,X19)
        | X19 != k2_tarski(X17,X18) )
      & ( X21 != X18
        | r2_hidden(X21,X19)
        | X19 != k2_tarski(X17,X18) )
      & ( esk2_3(X22,X23,X24) != X22
        | ~ r2_hidden(esk2_3(X22,X23,X24),X24)
        | X24 = k2_tarski(X22,X23) )
      & ( esk2_3(X22,X23,X24) != X23
        | ~ r2_hidden(esk2_3(X22,X23,X24),X24)
        | X24 = k2_tarski(X22,X23) )
      & ( r2_hidden(esk2_3(X22,X23,X24),X24)
        | esk2_3(X22,X23,X24) = X22
        | esk2_3(X22,X23,X24) = X23
        | X24 = k2_tarski(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_6,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k1_enumset1(X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | esk2_3(X1,X2,X3) = X1
    | esk2_3(X1,X2,X3) = X2
    | X3 = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( esk2_3(X1,X2,k1_enumset1(X3,X4,X5)) = X1
    | esk2_3(X1,X2,k1_enumset1(X3,X4,X5)) = X2
    | esk2_3(X1,X2,k1_enumset1(X3,X4,X5)) = X5
    | esk2_3(X1,X2,k1_enumset1(X3,X4,X5)) = X4
    | esk2_3(X1,X2,k1_enumset1(X3,X4,X5)) = X3
    | k1_enumset1(X3,X4,X5) = k2_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_11,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( X3 = k2_tarski(X1,X2)
    | esk2_3(X1,X2,X3) != X1
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( esk2_3(X1,X2,k1_enumset1(X3,X4,X1)) = X3
    | esk2_3(X1,X2,k1_enumset1(X3,X4,X1)) = X4
    | esk2_3(X1,X2,k1_enumset1(X3,X4,X1)) = X1
    | esk2_3(X1,X2,k1_enumset1(X3,X4,X1)) = X2
    | k1_enumset1(X3,X4,X1) = k2_tarski(X1,X2) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_9])])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_10])])).

cnf(c_0_15,plain,
    ( esk2_3(X1,X2,k2_tarski(X3,X4)) = X1
    | esk2_3(X1,X2,k2_tarski(X3,X4)) = X2
    | esk2_3(X1,X2,k2_tarski(X3,X4)) = X4
    | esk2_3(X1,X2,k2_tarski(X3,X4)) = X3
    | k2_tarski(X3,X4) = k2_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_7])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( esk2_3(X1,X2,k1_enumset1(X3,X4,X1)) = X2
    | esk2_3(X1,X2,k1_enumset1(X3,X4,X1)) = X4
    | esk2_3(X1,X2,k1_enumset1(X3,X4,X1)) = X3
    | k1_enumset1(X3,X4,X1) = k2_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_19,plain,
    ( esk2_3(X1,X2,k2_tarski(X3,X1)) = X3
    | esk2_3(X1,X2,k2_tarski(X3,X1)) = X1
    | esk2_3(X1,X2,k2_tarski(X3,X1)) = X2
    | k2_tarski(X3,X1) = k2_tarski(X1,X2) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_15])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_16])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(assume_negation,[status(cth)],[t70_enumset1])).

cnf(c_0_22,plain,
    ( X3 = k2_tarski(X1,X2)
    | esk2_3(X1,X2,X3) != X2
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,plain,
    ( esk2_3(X1,X2,k1_enumset1(X3,X2,X1)) = X3
    | esk2_3(X1,X2,k1_enumset1(X3,X2,X1)) = X2
    | k1_enumset1(X3,X2,X1) = k2_tarski(X1,X2) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_17])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X1,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_26,plain,
    ( esk2_3(X1,X2,k2_tarski(X3,X1)) = X2
    | esk2_3(X1,X2,k2_tarski(X3,X1)) = X3
    | k2_tarski(X3,X1) = k2_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_19]),c_0_20])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_28,negated_conjecture,(
    k1_enumset1(esk3_0,esk3_0,esk4_0) != k2_tarski(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_29,plain,
    ( esk2_3(X1,X2,k1_enumset1(X3,X2,X1)) = X3
    | k1_enumset1(X3,X2,X1) = k2_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_25])])).

cnf(c_0_31,plain,
    ( esk2_3(X1,X2,k2_tarski(X2,X1)) = X2
    | k2_tarski(X2,X1) = k2_tarski(X1,X2) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_26])])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_27])])).

cnf(c_0_33,negated_conjecture,
    ( k1_enumset1(esk3_0,esk3_0,esk4_0) != k2_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X2,X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_29]),c_0_30])])])).

cnf(c_0_35,plain,
    ( k1_enumset1(X1,X2,X1) = k2_tarski(X1,X2) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_29]),c_0_30])])])).

cnf(c_0_36,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_31]),c_0_32])])).

cnf(c_0_37,negated_conjecture,
    ( k1_enumset1(esk4_0,esk4_0,esk3_0) != k1_enumset1(esk3_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X1,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( k1_enumset1(esk3_0,esk4_0,esk3_0) != k1_enumset1(esk3_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,plain,
    ( k1_enumset1(X1,X2,X1) = k1_enumset1(X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:32:37 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.44  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.44  #
% 0.20/0.44  # Preprocessing time       : 0.028 s
% 0.20/0.44  # Presaturation interreduction done
% 0.20/0.44  
% 0.20/0.44  # Proof found!
% 0.20/0.44  # SZS status Theorem
% 0.20/0.44  # SZS output start CNFRefutation
% 0.20/0.44  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.20/0.44  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.20/0.44  fof(t70_enumset1, conjecture, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.44  fof(c_0_3, plain, ![X6, X7, X8, X9, X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X10,X9)|(X10=X6|X10=X7|X10=X8)|X9!=k1_enumset1(X6,X7,X8))&(((X11!=X6|r2_hidden(X11,X9)|X9!=k1_enumset1(X6,X7,X8))&(X11!=X7|r2_hidden(X11,X9)|X9!=k1_enumset1(X6,X7,X8)))&(X11!=X8|r2_hidden(X11,X9)|X9!=k1_enumset1(X6,X7,X8))))&((((esk1_4(X12,X13,X14,X15)!=X12|~r2_hidden(esk1_4(X12,X13,X14,X15),X15)|X15=k1_enumset1(X12,X13,X14))&(esk1_4(X12,X13,X14,X15)!=X13|~r2_hidden(esk1_4(X12,X13,X14,X15),X15)|X15=k1_enumset1(X12,X13,X14)))&(esk1_4(X12,X13,X14,X15)!=X14|~r2_hidden(esk1_4(X12,X13,X14,X15),X15)|X15=k1_enumset1(X12,X13,X14)))&(r2_hidden(esk1_4(X12,X13,X14,X15),X15)|(esk1_4(X12,X13,X14,X15)=X12|esk1_4(X12,X13,X14,X15)=X13|esk1_4(X12,X13,X14,X15)=X14)|X15=k1_enumset1(X12,X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.20/0.44  cnf(c_0_4, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.44  fof(c_0_5, plain, ![X17, X18, X19, X20, X21, X22, X23, X24]:(((~r2_hidden(X20,X19)|(X20=X17|X20=X18)|X19!=k2_tarski(X17,X18))&((X21!=X17|r2_hidden(X21,X19)|X19!=k2_tarski(X17,X18))&(X21!=X18|r2_hidden(X21,X19)|X19!=k2_tarski(X17,X18))))&(((esk2_3(X22,X23,X24)!=X22|~r2_hidden(esk2_3(X22,X23,X24),X24)|X24=k2_tarski(X22,X23))&(esk2_3(X22,X23,X24)!=X23|~r2_hidden(esk2_3(X22,X23,X24),X24)|X24=k2_tarski(X22,X23)))&(r2_hidden(esk2_3(X22,X23,X24),X24)|(esk2_3(X22,X23,X24)=X22|esk2_3(X22,X23,X24)=X23)|X24=k2_tarski(X22,X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.20/0.44  cnf(c_0_6, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k1_enumset1(X4,X3,X2))), inference(er,[status(thm)],[c_0_4])).
% 0.20/0.44  cnf(c_0_7, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|esk2_3(X1,X2,X3)=X1|esk2_3(X1,X2,X3)=X2|X3=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.44  cnf(c_0_8, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.44  cnf(c_0_9, plain, (esk2_3(X1,X2,k1_enumset1(X3,X4,X5))=X1|esk2_3(X1,X2,k1_enumset1(X3,X4,X5))=X2|esk2_3(X1,X2,k1_enumset1(X3,X4,X5))=X5|esk2_3(X1,X2,k1_enumset1(X3,X4,X5))=X4|esk2_3(X1,X2,k1_enumset1(X3,X4,X5))=X3|k1_enumset1(X3,X4,X5)=k2_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.20/0.44  cnf(c_0_10, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.44  cnf(c_0_11, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_tarski(X3,X2))), inference(er,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_12, plain, (X3=k2_tarski(X1,X2)|esk2_3(X1,X2,X3)!=X1|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.44  cnf(c_0_13, plain, (esk2_3(X1,X2,k1_enumset1(X3,X4,X1))=X3|esk2_3(X1,X2,k1_enumset1(X3,X4,X1))=X4|esk2_3(X1,X2,k1_enumset1(X3,X4,X1))=X1|esk2_3(X1,X2,k1_enumset1(X3,X4,X1))=X2|k1_enumset1(X3,X4,X1)=k2_tarski(X1,X2)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_9])])).
% 0.20/0.44  cnf(c_0_14, plain, (r2_hidden(X1,k1_enumset1(X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_10])])).
% 0.20/0.44  cnf(c_0_15, plain, (esk2_3(X1,X2,k2_tarski(X3,X4))=X1|esk2_3(X1,X2,k2_tarski(X3,X4))=X2|esk2_3(X1,X2,k2_tarski(X3,X4))=X4|esk2_3(X1,X2,k2_tarski(X3,X4))=X3|k2_tarski(X3,X4)=k2_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_11, c_0_7])).
% 0.20/0.44  cnf(c_0_16, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.44  cnf(c_0_17, plain, (esk2_3(X1,X2,k1_enumset1(X3,X4,X1))=X2|esk2_3(X1,X2,k1_enumset1(X3,X4,X1))=X4|esk2_3(X1,X2,k1_enumset1(X3,X4,X1))=X3|k1_enumset1(X3,X4,X1)=k2_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])])).
% 0.20/0.44  cnf(c_0_18, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.44  cnf(c_0_19, plain, (esk2_3(X1,X2,k2_tarski(X3,X1))=X3|esk2_3(X1,X2,k2_tarski(X3,X1))=X1|esk2_3(X1,X2,k2_tarski(X3,X1))=X2|k2_tarski(X3,X1)=k2_tarski(X1,X2)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_15])])).
% 0.20/0.44  cnf(c_0_20, plain, (r2_hidden(X1,k2_tarski(X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_16])])).
% 0.20/0.44  fof(c_0_21, negated_conjecture, ~(![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(assume_negation,[status(cth)],[t70_enumset1])).
% 0.20/0.44  cnf(c_0_22, plain, (X3=k2_tarski(X1,X2)|esk2_3(X1,X2,X3)!=X2|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.44  cnf(c_0_23, plain, (esk2_3(X1,X2,k1_enumset1(X3,X2,X1))=X3|esk2_3(X1,X2,k1_enumset1(X3,X2,X1))=X2|k1_enumset1(X3,X2,X1)=k2_tarski(X1,X2)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_17])])).
% 0.20/0.44  cnf(c_0_24, plain, (r2_hidden(X1,k1_enumset1(X2,X1,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_18])])).
% 0.20/0.44  cnf(c_0_25, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.44  cnf(c_0_26, plain, (esk2_3(X1,X2,k2_tarski(X3,X1))=X2|esk2_3(X1,X2,k2_tarski(X3,X1))=X3|k2_tarski(X3,X1)=k2_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_19]), c_0_20])])).
% 0.20/0.44  cnf(c_0_27, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.44  fof(c_0_28, negated_conjecture, k1_enumset1(esk3_0,esk3_0,esk4_0)!=k2_tarski(esk3_0,esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.20/0.44  cnf(c_0_29, plain, (esk2_3(X1,X2,k1_enumset1(X3,X2,X1))=X3|k1_enumset1(X3,X2,X1)=k2_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.20/0.44  cnf(c_0_30, plain, (r2_hidden(X1,k1_enumset1(X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_25])])).
% 0.20/0.44  cnf(c_0_31, plain, (esk2_3(X1,X2,k2_tarski(X2,X1))=X2|k2_tarski(X2,X1)=k2_tarski(X1,X2)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_26])])).
% 0.20/0.44  cnf(c_0_32, plain, (r2_hidden(X1,k2_tarski(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_27])])).
% 0.20/0.44  cnf(c_0_33, negated_conjecture, (k1_enumset1(esk3_0,esk3_0,esk4_0)!=k2_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.44  cnf(c_0_34, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X2,X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_29]), c_0_30])])])).
% 0.20/0.44  cnf(c_0_35, plain, (k1_enumset1(X1,X2,X1)=k2_tarski(X1,X2)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_29]), c_0_30])])])).
% 0.20/0.44  cnf(c_0_36, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_31]), c_0_32])])).
% 0.20/0.44  cnf(c_0_37, negated_conjecture, (k1_enumset1(esk4_0,esk4_0,esk3_0)!=k1_enumset1(esk3_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.44  cnf(c_0_38, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X1,X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.44  cnf(c_0_39, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_36, c_0_34])).
% 0.20/0.44  cnf(c_0_40, negated_conjecture, (k1_enumset1(esk3_0,esk4_0,esk3_0)!=k1_enumset1(esk3_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.44  cnf(c_0_41, plain, (k1_enumset1(X1,X2,X1)=k1_enumset1(X1,X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_39])).
% 0.20/0.44  cnf(c_0_42, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41])]), ['proof']).
% 0.20/0.44  # SZS output end CNFRefutation
% 0.20/0.44  # Proof object total steps             : 43
% 0.20/0.44  # Proof object clause steps            : 36
% 0.20/0.44  # Proof object formula steps           : 7
% 0.20/0.44  # Proof object conjectures             : 7
% 0.20/0.44  # Proof object clause conjectures      : 4
% 0.20/0.44  # Proof object formula conjectures     : 3
% 0.20/0.44  # Proof object initial clauses used    : 11
% 0.20/0.44  # Proof object initial formulas used   : 3
% 0.20/0.44  # Proof object generating inferences   : 15
% 0.20/0.44  # Proof object simplifying inferences  : 34
% 0.20/0.44  # Training examples: 0 positive, 0 negative
% 0.20/0.44  # Parsed axioms                        : 3
% 0.20/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.44  # Initial clauses                      : 15
% 0.20/0.44  # Removed in clause preprocessing      : 0
% 0.20/0.44  # Initial clauses in saturation        : 15
% 0.20/0.44  # Processed clauses                    : 579
% 0.20/0.44  # ...of these trivial                  : 7
% 0.20/0.44  # ...subsumed                          : 407
% 0.20/0.44  # ...remaining for further processing  : 165
% 0.20/0.44  # Other redundant clauses eliminated   : 584
% 0.20/0.44  # Clauses deleted for lack of memory   : 0
% 0.20/0.44  # Backward-subsumed                    : 24
% 0.20/0.44  # Backward-rewritten                   : 3
% 0.20/0.44  # Generated clauses                    : 2779
% 0.20/0.44  # ...of the previous two non-trivial   : 1916
% 0.20/0.44  # Contextual simplify-reflections      : 0
% 0.20/0.44  # Paramodulations                      : 1862
% 0.20/0.44  # Factorizations                       : 338
% 0.20/0.44  # Equation resolutions                 : 584
% 0.20/0.44  # Propositional unsat checks           : 0
% 0.20/0.44  #    Propositional check models        : 0
% 0.20/0.44  #    Propositional check unsatisfiable : 0
% 0.20/0.44  #    Propositional clauses             : 0
% 0.20/0.44  #    Propositional clauses after purity: 0
% 0.20/0.44  #    Propositional unsat core size     : 0
% 0.20/0.44  #    Propositional preprocessing time  : 0.000
% 0.20/0.44  #    Propositional encoding time       : 0.000
% 0.20/0.44  #    Propositional solver time         : 0.000
% 0.20/0.44  #    Success case prop preproc time    : 0.000
% 0.20/0.44  #    Success case prop encoding time   : 0.000
% 0.20/0.44  #    Success case prop solver time     : 0.000
% 0.20/0.44  # Current number of processed clauses  : 116
% 0.20/0.44  #    Positive orientable unit clauses  : 5
% 0.20/0.44  #    Positive unorientable unit clauses: 7
% 0.20/0.44  #    Negative unit clauses             : 0
% 0.20/0.44  #    Non-unit-clauses                  : 104
% 0.20/0.44  # Current number of unprocessed clauses: 1245
% 0.20/0.44  # ...number of literals in the above   : 6833
% 0.20/0.44  # Current number of archived formulas  : 0
% 0.20/0.44  # Current number of archived clauses   : 42
% 0.20/0.44  # Clause-clause subsumption calls (NU) : 6775
% 0.20/0.44  # Rec. Clause-clause subsumption calls : 1488
% 0.20/0.44  # Non-unit clause-clause subsumptions  : 382
% 0.20/0.44  # Unit Clause-clause subsumption calls : 366
% 0.20/0.44  # Rewrite failures with RHS unbound    : 0
% 0.20/0.44  # BW rewrite match attempts            : 339
% 0.20/0.44  # BW rewrite match successes           : 150
% 0.20/0.44  # Condensation attempts                : 0
% 0.20/0.44  # Condensation successes               : 0
% 0.20/0.44  # Termbank termtop insertions          : 35311
% 0.20/0.44  
% 0.20/0.44  # -------------------------------------------------
% 0.20/0.44  # User time                : 0.089 s
% 0.20/0.44  # System time              : 0.004 s
% 0.20/0.44  # Total time               : 0.093 s
% 0.20/0.44  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
