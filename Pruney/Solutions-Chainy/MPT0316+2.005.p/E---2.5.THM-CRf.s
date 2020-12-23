%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:42 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   30 (  81 expanded)
%              Number of clauses        :   19 (  36 expanded)
%              Number of leaves         :    5 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :  102 ( 249 expanded)
%              Number of equality atoms :   46 (  98 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t128_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))
    <=> ( X1 = X3
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))
      <=> ( X1 = X3
          & r2_hidden(X2,X4) ) ) ),
    inference(assume_negation,[status(cth)],[t128_zfmisc_1])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X7,X6)
        | X7 = X5
        | X6 != k1_tarski(X5) )
      & ( X8 != X5
        | r2_hidden(X8,X6)
        | X6 != k1_tarski(X5) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) != X9
        | X10 = k1_tarski(X9) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) = X9
        | X10 = k1_tarski(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_7,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_8,negated_conjecture,
    ( ( ~ r2_hidden(k4_tarski(esk3_0,esk4_0),k2_zfmisc_1(k1_tarski(esk5_0),esk6_0))
      | esk3_0 != esk5_0
      | ~ r2_hidden(esk4_0,esk6_0) )
    & ( esk3_0 = esk5_0
      | r2_hidden(k4_tarski(esk3_0,esk4_0),k2_zfmisc_1(k1_tarski(esk5_0),esk6_0)) )
    & ( r2_hidden(esk4_0,esk6_0)
      | r2_hidden(k4_tarski(esk3_0,esk4_0),k2_zfmisc_1(k1_tarski(esk5_0),esk6_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

cnf(c_0_9,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X22,X23,X24,X25] :
      ( ( r2_hidden(X22,X24)
        | ~ r2_hidden(k4_tarski(X22,X23),k2_zfmisc_1(X24,X25)) )
      & ( r2_hidden(X23,X25)
        | ~ r2_hidden(k4_tarski(X22,X23),k2_zfmisc_1(X24,X25)) )
      & ( ~ r2_hidden(X22,X24)
        | ~ r2_hidden(X23,X25)
        | r2_hidden(k4_tarski(X22,X23),k2_zfmisc_1(X24,X25)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | r2_hidden(k4_tarski(esk3_0,esk4_0),k2_zfmisc_1(k1_tarski(esk5_0),esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( esk3_0 = esk5_0
    | r2_hidden(k4_tarski(esk3_0,esk4_0),k2_zfmisc_1(k1_tarski(esk5_0),esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( X1 = X3
    | X2 != k2_tarski(X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk3_0,esk4_0),k2_zfmisc_1(k1_tarski(esk5_0),esk6_0))
    | esk3_0 != esk5_0
    | ~ r2_hidden(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | r2_hidden(k4_tarski(esk3_0,esk4_0),k2_zfmisc_1(k2_tarski(esk5_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_10])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( esk5_0 = esk3_0
    | r2_hidden(k4_tarski(esk3_0,esk4_0),k2_zfmisc_1(k2_tarski(esk5_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_10])).

cnf(c_0_20,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X12
        | X15 = X13
        | X14 != k2_tarski(X12,X13) )
      & ( X16 != X12
        | r2_hidden(X16,X14)
        | X14 != k2_tarski(X12,X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k2_tarski(X12,X13) )
      & ( esk2_3(X17,X18,X19) != X17
        | ~ r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k2_tarski(X17,X18) )
      & ( esk2_3(X17,X18,X19) != X18
        | ~ r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k2_tarski(X17,X18) )
      & ( r2_hidden(esk2_3(X17,X18,X19),X19)
        | esk2_3(X17,X18,X19) = X17
        | esk2_3(X17,X18,X19) = X18
        | X19 = k2_tarski(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_22,negated_conjecture,
    ( esk5_0 != esk3_0
    | ~ r2_hidden(esk4_0,esk6_0)
    | ~ r2_hidden(k4_tarski(esk3_0,esk4_0),k2_zfmisc_1(k2_tarski(esk5_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( esk3_0 = esk5_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk5_0,esk4_0),k2_zfmisc_1(k2_tarski(esk5_0,esk5_0),esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23])]),c_0_24]),c_0_24])])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_25])])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_23]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:31:42 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.34  # Version: 2.5pre002
% 0.18/0.34  # No SInE strategy applied
% 0.18/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.027 s
% 0.18/0.36  # Presaturation interreduction done
% 0.18/0.36  
% 0.18/0.36  # Proof found!
% 0.18/0.36  # SZS status Theorem
% 0.18/0.36  # SZS output start CNFRefutation
% 0.18/0.36  fof(t128_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))<=>(X1=X3&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 0.18/0.36  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.18/0.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.36  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.18/0.36  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.18/0.36  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))<=>(X1=X3&r2_hidden(X2,X4)))), inference(assume_negation,[status(cth)],[t128_zfmisc_1])).
% 0.18/0.36  fof(c_0_6, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.18/0.36  fof(c_0_7, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.36  fof(c_0_8, negated_conjecture, ((~r2_hidden(k4_tarski(esk3_0,esk4_0),k2_zfmisc_1(k1_tarski(esk5_0),esk6_0))|(esk3_0!=esk5_0|~r2_hidden(esk4_0,esk6_0)))&((esk3_0=esk5_0|r2_hidden(k4_tarski(esk3_0,esk4_0),k2_zfmisc_1(k1_tarski(esk5_0),esk6_0)))&(r2_hidden(esk4_0,esk6_0)|r2_hidden(k4_tarski(esk3_0,esk4_0),k2_zfmisc_1(k1_tarski(esk5_0),esk6_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.18/0.36  cnf(c_0_9, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.36  cnf(c_0_10, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.36  fof(c_0_11, plain, ![X22, X23, X24, X25]:(((r2_hidden(X22,X24)|~r2_hidden(k4_tarski(X22,X23),k2_zfmisc_1(X24,X25)))&(r2_hidden(X23,X25)|~r2_hidden(k4_tarski(X22,X23),k2_zfmisc_1(X24,X25))))&(~r2_hidden(X22,X24)|~r2_hidden(X23,X25)|r2_hidden(k4_tarski(X22,X23),k2_zfmisc_1(X24,X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.18/0.36  cnf(c_0_12, negated_conjecture, (r2_hidden(esk4_0,esk6_0)|r2_hidden(k4_tarski(esk3_0,esk4_0),k2_zfmisc_1(k1_tarski(esk5_0),esk6_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.36  cnf(c_0_13, negated_conjecture, (esk3_0=esk5_0|r2_hidden(k4_tarski(esk3_0,esk4_0),k2_zfmisc_1(k1_tarski(esk5_0),esk6_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.36  cnf(c_0_14, plain, (X1=X3|X2!=k2_tarski(X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.18/0.36  cnf(c_0_15, negated_conjecture, (~r2_hidden(k4_tarski(esk3_0,esk4_0),k2_zfmisc_1(k1_tarski(esk5_0),esk6_0))|esk3_0!=esk5_0|~r2_hidden(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.36  cnf(c_0_16, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.36  cnf(c_0_17, negated_conjecture, (r2_hidden(esk4_0,esk6_0)|r2_hidden(k4_tarski(esk3_0,esk4_0),k2_zfmisc_1(k2_tarski(esk5_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_12, c_0_10])).
% 0.18/0.36  cnf(c_0_18, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.36  cnf(c_0_19, negated_conjecture, (esk5_0=esk3_0|r2_hidden(k4_tarski(esk3_0,esk4_0),k2_zfmisc_1(k2_tarski(esk5_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_13, c_0_10])).
% 0.18/0.36  cnf(c_0_20, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(er,[status(thm)],[c_0_14])).
% 0.18/0.36  fof(c_0_21, plain, ![X12, X13, X14, X15, X16, X17, X18, X19]:(((~r2_hidden(X15,X14)|(X15=X12|X15=X13)|X14!=k2_tarski(X12,X13))&((X16!=X12|r2_hidden(X16,X14)|X14!=k2_tarski(X12,X13))&(X16!=X13|r2_hidden(X16,X14)|X14!=k2_tarski(X12,X13))))&(((esk2_3(X17,X18,X19)!=X17|~r2_hidden(esk2_3(X17,X18,X19),X19)|X19=k2_tarski(X17,X18))&(esk2_3(X17,X18,X19)!=X18|~r2_hidden(esk2_3(X17,X18,X19),X19)|X19=k2_tarski(X17,X18)))&(r2_hidden(esk2_3(X17,X18,X19),X19)|(esk2_3(X17,X18,X19)=X17|esk2_3(X17,X18,X19)=X18)|X19=k2_tarski(X17,X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.18/0.36  cnf(c_0_22, negated_conjecture, (esk5_0!=esk3_0|~r2_hidden(esk4_0,esk6_0)|~r2_hidden(k4_tarski(esk3_0,esk4_0),k2_zfmisc_1(k2_tarski(esk5_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_15, c_0_10])).
% 0.18/0.36  cnf(c_0_23, negated_conjecture, (r2_hidden(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.18/0.36  cnf(c_0_24, negated_conjecture, (esk3_0=esk5_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.18/0.36  cnf(c_0_25, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.36  cnf(c_0_26, negated_conjecture, (~r2_hidden(k4_tarski(esk5_0,esk4_0),k2_zfmisc_1(k2_tarski(esk5_0,esk5_0),esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23])]), c_0_24]), c_0_24])])).
% 0.18/0.36  cnf(c_0_27, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.36  cnf(c_0_28, plain, (r2_hidden(X1,k2_tarski(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_25])])).
% 0.18/0.36  cnf(c_0_29, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_23]), c_0_28])]), ['proof']).
% 0.18/0.36  # SZS output end CNFRefutation
% 0.18/0.36  # Proof object total steps             : 30
% 0.18/0.36  # Proof object clause steps            : 19
% 0.18/0.36  # Proof object formula steps           : 11
% 0.18/0.36  # Proof object conjectures             : 13
% 0.18/0.36  # Proof object clause conjectures      : 10
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 9
% 0.18/0.36  # Proof object initial formulas used   : 5
% 0.18/0.36  # Proof object generating inferences   : 3
% 0.18/0.36  # Proof object simplifying inferences  : 16
% 0.18/0.36  # Training examples: 0 positive, 0 negative
% 0.18/0.36  # Parsed axioms                        : 5
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 17
% 0.18/0.36  # Removed in clause preprocessing      : 1
% 0.18/0.36  # Initial clauses in saturation        : 16
% 0.18/0.36  # Processed clauses                    : 37
% 0.18/0.36  # ...of these trivial                  : 1
% 0.18/0.36  # ...subsumed                          : 0
% 0.18/0.36  # ...remaining for further processing  : 36
% 0.18/0.36  # Other redundant clauses eliminated   : 8
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 0
% 0.18/0.36  # Backward-rewritten                   : 3
% 0.18/0.36  # Generated clauses                    : 14
% 0.18/0.36  # ...of the previous two non-trivial   : 9
% 0.18/0.36  # Contextual simplify-reflections      : 1
% 0.18/0.36  # Paramodulations                      : 9
% 0.18/0.36  # Factorizations                       : 0
% 0.18/0.36  # Equation resolutions                 : 8
% 0.18/0.36  # Propositional unsat checks           : 0
% 0.18/0.36  #    Propositional check models        : 0
% 0.18/0.36  #    Propositional check unsatisfiable : 0
% 0.18/0.36  #    Propositional clauses             : 0
% 0.18/0.36  #    Propositional clauses after purity: 0
% 0.18/0.36  #    Propositional unsat core size     : 0
% 0.18/0.36  #    Propositional preprocessing time  : 0.000
% 0.18/0.36  #    Propositional encoding time       : 0.000
% 0.18/0.36  #    Propositional solver time         : 0.000
% 0.18/0.36  #    Success case prop preproc time    : 0.000
% 0.18/0.36  #    Success case prop encoding time   : 0.000
% 0.18/0.36  #    Success case prop solver time     : 0.000
% 0.18/0.36  # Current number of processed clauses  : 13
% 0.18/0.36  #    Positive orientable unit clauses  : 4
% 0.18/0.36  #    Positive unorientable unit clauses: 0
% 0.18/0.36  #    Negative unit clauses             : 1
% 0.18/0.36  #    Non-unit-clauses                  : 8
% 0.18/0.36  # Current number of unprocessed clauses: 3
% 0.18/0.36  # ...number of literals in the above   : 9
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 19
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 70
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 65
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 1
% 0.18/0.36  # Unit Clause-clause subsumption calls : 5
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 7
% 0.18/0.36  # BW rewrite match successes           : 2
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 1256
% 0.18/0.37  
% 0.18/0.37  # -------------------------------------------------
% 0.18/0.37  # User time                : 0.024 s
% 0.18/0.37  # System time              : 0.008 s
% 0.18/0.37  # Total time               : 0.032 s
% 0.18/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
