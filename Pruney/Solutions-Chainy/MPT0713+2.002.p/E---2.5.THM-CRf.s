%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:41 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 148 expanded)
%              Number of clauses        :   30 (  57 expanded)
%              Number of leaves         :    8 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  128 ( 380 expanded)
%              Number of equality atoms :   49 ( 149 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t168_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => k2_relat_1(k7_relat_1(X2,k1_tarski(X1))) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r2_hidden(X1,k1_relat_1(X2))
         => k2_relat_1(k7_relat_1(X2,k1_tarski(X1))) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t168_funct_1])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r2_hidden(esk2_0,k1_relat_1(esk3_0))
    & k2_relat_1(k7_relat_1(esk3_0,k1_tarski(esk2_0))) != k1_tarski(k1_funct_1(esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_10,plain,(
    ! [X11] : k2_tarski(X11,X11) = k1_tarski(X11) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_12,plain,(
    ! [X4,X5,X6,X7,X8,X9] :
      ( ( ~ r2_hidden(X6,X5)
        | X6 = X4
        | X5 != k1_tarski(X4) )
      & ( X7 != X4
        | r2_hidden(X7,X5)
        | X5 != k1_tarski(X4) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | esk1_2(X8,X9) != X8
        | X9 = k1_tarski(X8) )
      & ( r2_hidden(esk1_2(X8,X9),X9)
        | esk1_2(X8,X9) = X8
        | X9 = k1_tarski(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_13,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk3_0,k1_tarski(esk2_0))) != k1_tarski(k1_funct_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk3_0,k1_enumset1(esk2_0,esk2_0,esk2_0))) != k1_enumset1(k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14]),c_0_15]),c_0_15])).

cnf(c_0_18,plain,
    ( esk1_2(X1,X2) = X1
    | X2 = k1_enumset1(X1,X1,X1)
    | r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_14]),c_0_15])).

fof(c_0_19,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | k2_relat_1(k7_relat_1(X17,X16)) = k9_relat_1(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_20,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | k11_relat_1(X14,X15) = k9_relat_1(X14,k1_tarski(X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

cnf(c_0_21,negated_conjecture,
    ( esk1_2(k1_funct_1(esk3_0,esk2_0),k2_relat_1(k7_relat_1(esk3_0,k1_enumset1(esk2_0,esk2_0,esk2_0)))) = k1_funct_1(esk3_0,esk2_0)
    | r2_hidden(esk1_2(k1_funct_1(esk3_0,esk2_0),k2_relat_1(k7_relat_1(esk3_0,k1_enumset1(esk2_0,esk2_0,esk2_0)))),k2_relat_1(k7_relat_1(esk3_0,k1_enumset1(esk2_0,esk2_0,esk2_0)))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18])])).

cnf(c_0_22,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X18,X19,X20] :
      ( ( ~ r2_hidden(k4_tarski(X18,X19),X20)
        | r2_hidden(X19,k11_relat_1(X20,X18))
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(X19,k11_relat_1(X20,X18))
        | r2_hidden(k4_tarski(X18,X19),X20)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

cnf(c_0_26,negated_conjecture,
    ( esk1_2(k1_funct_1(esk3_0,esk2_0),k9_relat_1(esk3_0,k1_enumset1(esk2_0,esk2_0,esk2_0))) = k1_funct_1(esk3_0,esk2_0)
    | r2_hidden(esk1_2(k1_funct_1(esk3_0,esk2_0),k9_relat_1(esk3_0,k1_enumset1(esk2_0,esk2_0,esk2_0))),k9_relat_1(esk3_0,k1_enumset1(esk2_0,esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_27,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_enumset1(X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_14]),c_0_15])).

fof(c_0_28,plain,(
    ! [X21,X22,X23] :
      ( ( r2_hidden(X21,k1_relat_1(X23))
        | ~ r2_hidden(k4_tarski(X21,X22),X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( X22 = k1_funct_1(X23,X21)
        | ~ r2_hidden(k4_tarski(X21,X22),X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( ~ r2_hidden(X21,k1_relat_1(X23))
        | X22 != k1_funct_1(X23,X21)
        | r2_hidden(k4_tarski(X21,X22),X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( esk1_2(k1_funct_1(esk3_0,esk2_0),k11_relat_1(esk3_0,esk2_0)) = k1_funct_1(esk3_0,esk2_0)
    | r2_hidden(esk1_2(k1_funct_1(esk3_0,esk2_0),k11_relat_1(esk3_0,esk2_0)),k11_relat_1(esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_23])])).

cnf(c_0_31,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( esk1_2(k1_funct_1(esk3_0,esk2_0),k11_relat_1(esk3_0,esk2_0)) = k1_funct_1(esk3_0,esk2_0)
    | r2_hidden(k4_tarski(esk2_0,esk1_2(k1_funct_1(esk3_0,esk2_0),k11_relat_1(esk3_0,esk2_0))),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_23])])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,plain,
    ( X2 = k1_enumset1(X1,X1,X1)
    | esk1_2(X1,X2) != X1
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_14]),c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( esk1_2(k1_funct_1(esk3_0,esk2_0),k11_relat_1(esk3_0,esk2_0)) = k1_funct_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_23])])).

cnf(c_0_37,negated_conjecture,
    ( k1_enumset1(k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0)) = k11_relat_1(esk3_0,esk2_0)
    | ~ r2_hidden(k1_funct_1(esk3_0,esk2_0),k11_relat_1(esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_38,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk3_0,k1_enumset1(esk2_0,esk2_0,esk2_0))) != k11_relat_1(esk3_0,esk2_0)
    | ~ r2_hidden(k1_funct_1(esk3_0,esk2_0),k11_relat_1(esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_37])).

cnf(c_0_39,negated_conjecture,
    ( k9_relat_1(esk3_0,k1_enumset1(esk2_0,esk2_0,esk2_0)) != k11_relat_1(esk3_0,esk2_0)
    | ~ r2_hidden(k1_funct_1(esk3_0,esk2_0),k11_relat_1(esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_22]),c_0_23])])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk3_0,esk2_0),k11_relat_1(esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_27]),c_0_23])])).

cnf(c_0_41,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_42,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk2_0,k1_funct_1(esk3_0,esk2_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_23])])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk2_0,k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_34]),c_0_23]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.027 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(t168_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>k2_relat_1(k7_relat_1(X2,k1_tarski(X1)))=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_funct_1)).
% 0.21/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.21/0.38  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.21/0.38  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 0.21/0.38  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 0.21/0.38  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.21/0.38  fof(c_0_8, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>k2_relat_1(k7_relat_1(X2,k1_tarski(X1)))=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t168_funct_1])).
% 0.21/0.38  fof(c_0_9, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(r2_hidden(esk2_0,k1_relat_1(esk3_0))&k2_relat_1(k7_relat_1(esk3_0,k1_tarski(esk2_0)))!=k1_tarski(k1_funct_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.21/0.38  fof(c_0_10, plain, ![X11]:k2_tarski(X11,X11)=k1_tarski(X11), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.38  fof(c_0_11, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.38  fof(c_0_12, plain, ![X4, X5, X6, X7, X8, X9]:(((~r2_hidden(X6,X5)|X6=X4|X5!=k1_tarski(X4))&(X7!=X4|r2_hidden(X7,X5)|X5!=k1_tarski(X4)))&((~r2_hidden(esk1_2(X8,X9),X9)|esk1_2(X8,X9)!=X8|X9=k1_tarski(X8))&(r2_hidden(esk1_2(X8,X9),X9)|esk1_2(X8,X9)=X8|X9=k1_tarski(X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.21/0.38  cnf(c_0_13, negated_conjecture, (k2_relat_1(k7_relat_1(esk3_0,k1_tarski(esk2_0)))!=k1_tarski(k1_funct_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.38  cnf(c_0_14, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.38  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.38  cnf(c_0_16, plain, (r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.38  cnf(c_0_17, negated_conjecture, (k2_relat_1(k7_relat_1(esk3_0,k1_enumset1(esk2_0,esk2_0,esk2_0)))!=k1_enumset1(k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_14]), c_0_15]), c_0_15])).
% 0.21/0.38  cnf(c_0_18, plain, (esk1_2(X1,X2)=X1|X2=k1_enumset1(X1,X1,X1)|r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_14]), c_0_15])).
% 0.21/0.38  fof(c_0_19, plain, ![X16, X17]:(~v1_relat_1(X17)|k2_relat_1(k7_relat_1(X17,X16))=k9_relat_1(X17,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.21/0.38  fof(c_0_20, plain, ![X14, X15]:(~v1_relat_1(X14)|k11_relat_1(X14,X15)=k9_relat_1(X14,k1_tarski(X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.21/0.38  cnf(c_0_21, negated_conjecture, (esk1_2(k1_funct_1(esk3_0,esk2_0),k2_relat_1(k7_relat_1(esk3_0,k1_enumset1(esk2_0,esk2_0,esk2_0))))=k1_funct_1(esk3_0,esk2_0)|r2_hidden(esk1_2(k1_funct_1(esk3_0,esk2_0),k2_relat_1(k7_relat_1(esk3_0,k1_enumset1(esk2_0,esk2_0,esk2_0)))),k2_relat_1(k7_relat_1(esk3_0,k1_enumset1(esk2_0,esk2_0,esk2_0))))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18])])).
% 0.21/0.38  cnf(c_0_22, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.38  cnf(c_0_24, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.38  fof(c_0_25, plain, ![X18, X19, X20]:((~r2_hidden(k4_tarski(X18,X19),X20)|r2_hidden(X19,k11_relat_1(X20,X18))|~v1_relat_1(X20))&(~r2_hidden(X19,k11_relat_1(X20,X18))|r2_hidden(k4_tarski(X18,X19),X20)|~v1_relat_1(X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.21/0.38  cnf(c_0_26, negated_conjecture, (esk1_2(k1_funct_1(esk3_0,esk2_0),k9_relat_1(esk3_0,k1_enumset1(esk2_0,esk2_0,esk2_0)))=k1_funct_1(esk3_0,esk2_0)|r2_hidden(esk1_2(k1_funct_1(esk3_0,esk2_0),k9_relat_1(esk3_0,k1_enumset1(esk2_0,esk2_0,esk2_0))),k9_relat_1(esk3_0,k1_enumset1(esk2_0,esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.21/0.38  cnf(c_0_27, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_enumset1(X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_14]), c_0_15])).
% 0.21/0.38  fof(c_0_28, plain, ![X21, X22, X23]:(((r2_hidden(X21,k1_relat_1(X23))|~r2_hidden(k4_tarski(X21,X22),X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(X22=k1_funct_1(X23,X21)|~r2_hidden(k4_tarski(X21,X22),X23)|(~v1_relat_1(X23)|~v1_funct_1(X23))))&(~r2_hidden(X21,k1_relat_1(X23))|X22!=k1_funct_1(X23,X21)|r2_hidden(k4_tarski(X21,X22),X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.21/0.38  cnf(c_0_29, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.38  cnf(c_0_30, negated_conjecture, (esk1_2(k1_funct_1(esk3_0,esk2_0),k11_relat_1(esk3_0,esk2_0))=k1_funct_1(esk3_0,esk2_0)|r2_hidden(esk1_2(k1_funct_1(esk3_0,esk2_0),k11_relat_1(esk3_0,esk2_0)),k11_relat_1(esk3_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_23])])).
% 0.21/0.38  cnf(c_0_31, plain, (X2=k1_tarski(X1)|~r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.38  cnf(c_0_32, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.38  cnf(c_0_33, negated_conjecture, (esk1_2(k1_funct_1(esk3_0,esk2_0),k11_relat_1(esk3_0,esk2_0))=k1_funct_1(esk3_0,esk2_0)|r2_hidden(k4_tarski(esk2_0,esk1_2(k1_funct_1(esk3_0,esk2_0),k11_relat_1(esk3_0,esk2_0))),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_23])])).
% 0.21/0.38  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.38  cnf(c_0_35, plain, (X2=k1_enumset1(X1,X1,X1)|esk1_2(X1,X2)!=X1|~r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_14]), c_0_15])).
% 0.21/0.38  cnf(c_0_36, negated_conjecture, (esk1_2(k1_funct_1(esk3_0,esk2_0),k11_relat_1(esk3_0,esk2_0))=k1_funct_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_23])])).
% 0.21/0.38  cnf(c_0_37, negated_conjecture, (k1_enumset1(k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0))=k11_relat_1(esk3_0,esk2_0)|~r2_hidden(k1_funct_1(esk3_0,esk2_0),k11_relat_1(esk3_0,esk2_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.21/0.38  cnf(c_0_38, negated_conjecture, (k2_relat_1(k7_relat_1(esk3_0,k1_enumset1(esk2_0,esk2_0,esk2_0)))!=k11_relat_1(esk3_0,esk2_0)|~r2_hidden(k1_funct_1(esk3_0,esk2_0),k11_relat_1(esk3_0,esk2_0))), inference(spm,[status(thm)],[c_0_17, c_0_37])).
% 0.21/0.38  cnf(c_0_39, negated_conjecture, (k9_relat_1(esk3_0,k1_enumset1(esk2_0,esk2_0,esk2_0))!=k11_relat_1(esk3_0,esk2_0)|~r2_hidden(k1_funct_1(esk3_0,esk2_0),k11_relat_1(esk3_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_22]), c_0_23])])).
% 0.21/0.38  cnf(c_0_40, negated_conjecture, (~r2_hidden(k1_funct_1(esk3_0,esk2_0),k11_relat_1(esk3_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_27]), c_0_23])])).
% 0.21/0.38  cnf(c_0_41, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.38  cnf(c_0_42, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.38  cnf(c_0_43, negated_conjecture, (~r2_hidden(k4_tarski(esk2_0,k1_funct_1(esk3_0,esk2_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_23])])).
% 0.21/0.38  cnf(c_0_44, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_42])).
% 0.21/0.38  cnf(c_0_45, negated_conjecture, (r2_hidden(esk2_0,k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.38  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_34]), c_0_23]), c_0_45])]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 47
% 0.21/0.38  # Proof object clause steps            : 30
% 0.21/0.38  # Proof object formula steps           : 17
% 0.21/0.38  # Proof object conjectures             : 19
% 0.21/0.38  # Proof object clause conjectures      : 16
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 14
% 0.21/0.38  # Proof object initial formulas used   : 8
% 0.21/0.38  # Proof object generating inferences   : 11
% 0.21/0.38  # Proof object simplifying inferences  : 31
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 8
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 17
% 0.21/0.38  # Removed in clause preprocessing      : 2
% 0.21/0.38  # Initial clauses in saturation        : 15
% 0.21/0.38  # Processed clauses                    : 45
% 0.21/0.38  # ...of these trivial                  : 0
% 0.21/0.38  # ...subsumed                          : 1
% 0.21/0.38  # ...remaining for further processing  : 44
% 0.21/0.38  # Other redundant clauses eliminated   : 6
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 2
% 0.21/0.38  # Generated clauses                    : 93
% 0.21/0.38  # ...of the previous two non-trivial   : 82
% 0.21/0.38  # Contextual simplify-reflections      : 0
% 0.21/0.38  # Paramodulations                      : 88
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 6
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 24
% 0.21/0.38  #    Positive orientable unit clauses  : 5
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 3
% 0.21/0.38  #    Non-unit-clauses                  : 16
% 0.21/0.38  # Current number of unprocessed clauses: 66
% 0.21/0.38  # ...number of literals in the above   : 279
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 19
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 27
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 14
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.21/0.38  # Unit Clause-clause subsumption calls : 3
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 3
% 0.21/0.38  # BW rewrite match successes           : 1
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 2729
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.027 s
% 0.21/0.38  # System time              : 0.007 s
% 0.21/0.38  # Total time               : 0.034 s
% 0.21/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
