%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:56 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 130 expanded)
%              Number of clauses        :   32 (  54 expanded)
%              Number of leaves         :    5 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  144 ( 423 expanded)
%              Number of equality atoms :   66 ( 220 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t14_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(c_0_5,plain,(
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

fof(c_0_6,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_7,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( k1_relat_1(X2) = k1_tarski(X1)
         => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t14_funct_1])).

cnf(c_0_9,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & k1_relat_1(esk6_0) = k1_tarski(esk5_0)
    & k2_relat_1(esk6_0) != k1_tarski(k1_funct_1(esk6_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_13,plain,
    ( X1 = X3
    | X2 != k1_enumset1(X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_10]),c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X15,X16,X17,X19,X20,X21,X23] :
      ( ( r2_hidden(esk2_3(X15,X16,X17),k1_relat_1(X15))
        | ~ r2_hidden(X17,X16)
        | X16 != k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( X17 = k1_funct_1(X15,esk2_3(X15,X16,X17))
        | ~ r2_hidden(X17,X16)
        | X16 != k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( ~ r2_hidden(X20,k1_relat_1(X15))
        | X19 != k1_funct_1(X15,X20)
        | r2_hidden(X19,X16)
        | X16 != k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( ~ r2_hidden(esk3_2(X15,X21),X21)
        | ~ r2_hidden(X23,k1_relat_1(X15))
        | esk3_2(X15,X21) != k1_funct_1(X15,X23)
        | X21 = k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( r2_hidden(esk4_2(X15,X21),k1_relat_1(X15))
        | r2_hidden(esk3_2(X15,X21),X21)
        | X21 = k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( esk3_2(X15,X21) = k1_funct_1(X15,esk4_2(X15,X21))
        | r2_hidden(esk3_2(X15,X21),X21)
        | X21 = k2_relat_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_16,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_enumset1(X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_enumset1(esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_10]),c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( X1 = k1_funct_1(X2,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( X1 = esk5_0
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( k2_relat_1(esk6_0) != k1_tarski(k1_funct_1(esk6_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_26,plain,
    ( k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( esk2_3(esk6_0,k2_relat_1(esk6_0),X1) = esk5_0
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_28,negated_conjecture,
    ( k2_relat_1(esk6_0) != k1_enumset1(k1_funct_1(esk6_0,esk5_0),k1_funct_1(esk6_0,esk5_0),k1_funct_1(esk6_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_10]),c_0_11])).

cnf(c_0_29,plain,
    ( esk1_2(X1,X2) = X1
    | X2 = k1_enumset1(X1,X1,X1)
    | r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_10]),c_0_11])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_31,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_32,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_0) = X1
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_22]),c_0_23])])).

cnf(c_0_33,negated_conjecture,
    ( esk1_2(k1_funct_1(esk6_0,esk5_0),k2_relat_1(esk6_0)) = k1_funct_1(esk6_0,esk5_0)
    | r2_hidden(esk1_2(k1_funct_1(esk6_0,esk5_0),k2_relat_1(esk6_0)),k2_relat_1(esk6_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_10]),c_0_11])).

cnf(c_0_35,plain,
    ( X2 = k1_enumset1(X1,X1,X1)
    | esk1_2(X1,X2) != X1
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_10]),c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( esk1_2(k1_funct_1(esk6_0,esk5_0),k2_relat_1(esk6_0)) = k1_funct_1(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_relat_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_28])).

cnf(c_0_40,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_37])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_17])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_22]),c_0_23]),c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.035 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t14_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 0.13/0.38  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.13/0.38  fof(c_0_5, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.13/0.38  fof(c_0_6, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_7, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_8, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t14_funct_1])).
% 0.13/0.38  cnf(c_0_9, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_10, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_11, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  fof(c_0_12, negated_conjecture, ((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&(k1_relat_1(esk6_0)=k1_tarski(esk5_0)&k2_relat_1(esk6_0)!=k1_tarski(k1_funct_1(esk6_0,esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.13/0.38  cnf(c_0_13, plain, (X1=X3|X2!=k1_enumset1(X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9, c_0_10]), c_0_11])).
% 0.13/0.38  cnf(c_0_14, negated_conjecture, (k1_relat_1(esk6_0)=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  fof(c_0_15, plain, ![X15, X16, X17, X19, X20, X21, X23]:((((r2_hidden(esk2_3(X15,X16,X17),k1_relat_1(X15))|~r2_hidden(X17,X16)|X16!=k2_relat_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(X17=k1_funct_1(X15,esk2_3(X15,X16,X17))|~r2_hidden(X17,X16)|X16!=k2_relat_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15))))&(~r2_hidden(X20,k1_relat_1(X15))|X19!=k1_funct_1(X15,X20)|r2_hidden(X19,X16)|X16!=k2_relat_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15))))&((~r2_hidden(esk3_2(X15,X21),X21)|(~r2_hidden(X23,k1_relat_1(X15))|esk3_2(X15,X21)!=k1_funct_1(X15,X23))|X21=k2_relat_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15)))&((r2_hidden(esk4_2(X15,X21),k1_relat_1(X15))|r2_hidden(esk3_2(X15,X21),X21)|X21=k2_relat_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(esk3_2(X15,X21)=k1_funct_1(X15,esk4_2(X15,X21))|r2_hidden(esk3_2(X15,X21),X21)|X21=k2_relat_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.13/0.38  cnf(c_0_16, plain, (X1=X2|~r2_hidden(X1,k1_enumset1(X2,X2,X2))), inference(er,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (k1_relat_1(esk6_0)=k1_enumset1(esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_10]), c_0_11])).
% 0.13/0.38  cnf(c_0_18, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_19, plain, (X1=k1_funct_1(X2,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (X1=esk5_0|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.38  cnf(c_0_21, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (k2_relat_1(esk6_0)!=k1_tarski(k1_funct_1(esk6_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_25, plain, (r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_26, plain, (k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (esk2_3(esk6_0,k2_relat_1(esk6_0),X1)=esk5_0|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (k2_relat_1(esk6_0)!=k1_enumset1(k1_funct_1(esk6_0,esk5_0),k1_funct_1(esk6_0,esk5_0),k1_funct_1(esk6_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_10]), c_0_11])).
% 0.13/0.38  cnf(c_0_29, plain, (esk1_2(X1,X2)=X1|X2=k1_enumset1(X1,X1,X1)|r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_10]), c_0_11])).
% 0.13/0.38  cnf(c_0_30, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_31, plain, (X2=k1_tarski(X1)|~r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (k1_funct_1(esk6_0,esk5_0)=X1|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_22]), c_0_23])])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (esk1_2(k1_funct_1(esk6_0,esk5_0),k2_relat_1(esk6_0))=k1_funct_1(esk6_0,esk5_0)|r2_hidden(esk1_2(k1_funct_1(esk6_0,esk5_0),k2_relat_1(esk6_0)),k2_relat_1(esk6_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29])])).
% 0.13/0.38  cnf(c_0_34, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_10]), c_0_11])).
% 0.13/0.38  cnf(c_0_35, plain, (X2=k1_enumset1(X1,X1,X1)|esk1_2(X1,X2)!=X1|~r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_10]), c_0_11])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (esk1_2(k1_funct_1(esk6_0,esk5_0),k2_relat_1(esk6_0))=k1_funct_1(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.38  cnf(c_0_37, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_38, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (~r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_relat_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_28])).
% 0.13/0.39  cnf(c_0_40, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_37])])).
% 0.13/0.39  cnf(c_0_41, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_38, c_0_17])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_22]), c_0_23]), c_0_41])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 43
% 0.13/0.39  # Proof object clause steps            : 32
% 0.13/0.39  # Proof object formula steps           : 11
% 0.13/0.39  # Proof object conjectures             : 17
% 0.13/0.39  # Proof object clause conjectures      : 14
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 13
% 0.13/0.39  # Proof object initial formulas used   : 5
% 0.13/0.39  # Proof object generating inferences   : 8
% 0.13/0.39  # Proof object simplifying inferences  : 31
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 5
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 16
% 0.13/0.39  # Removed in clause preprocessing      : 2
% 0.13/0.39  # Initial clauses in saturation        : 14
% 0.13/0.39  # Processed clauses                    : 38
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 0
% 0.13/0.39  # ...remaining for further processing  : 38
% 0.13/0.39  # Other redundant clauses eliminated   : 9
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 1
% 0.13/0.39  # Generated clauses                    : 44
% 0.13/0.39  # ...of the previous two non-trivial   : 37
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 37
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 9
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 18
% 0.13/0.39  #    Positive orientable unit clauses  : 6
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 2
% 0.13/0.39  #    Non-unit-clauses                  : 10
% 0.13/0.39  # Current number of unprocessed clauses: 27
% 0.13/0.39  # ...number of literals in the above   : 123
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 17
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 85
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 32
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.39  # Unit Clause-clause subsumption calls : 0
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 3
% 0.13/0.39  # BW rewrite match successes           : 1
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 1743
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.038 s
% 0.13/0.39  # System time              : 0.005 s
% 0.13/0.39  # Total time               : 0.043 s
% 0.13/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
