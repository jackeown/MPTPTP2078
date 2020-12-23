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
% DateTime   : Thu Dec  3 10:52:13 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 230 expanded)
%              Number of clauses        :   37 ( 105 expanded)
%              Number of leaves         :    7 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :  147 ( 848 expanded)
%              Number of equality atoms :   65 ( 348 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t205_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(t151_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k9_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

fof(c_0_8,plain,(
    ! [X47,X48] :
      ( ( k9_relat_1(X48,X47) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X48),X47)
        | ~ v1_relat_1(X48) )
      & ( ~ r1_xboole_0(k1_relat_1(X48),X47)
        | k9_relat_1(X48,X47) = k1_xboole_0
        | ~ v1_relat_1(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk12_0)
    & ( ~ r2_hidden(esk11_0,k1_relat_1(esk12_0))
      | k11_relat_1(esk12_0,esk11_0) = k1_xboole_0 )
    & ( r2_hidden(esk11_0,k1_relat_1(esk12_0))
      | k11_relat_1(esk12_0,esk11_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | k11_relat_1(X26,X27) = k9_relat_1(X26,k1_tarski(X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_11,plain,(
    ! [X23] : k2_tarski(X23,X23) = k1_tarski(X23) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_13,plain,
    ( k9_relat_1(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r2_hidden(esk1_2(X6,X7),X6)
        | r1_xboole_0(X6,X7) )
      & ( r2_hidden(esk1_2(X6,X7),X7)
        | r1_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_16,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X16,X15)
        | X16 = X12
        | X16 = X13
        | X16 = X14
        | X15 != k1_enumset1(X12,X13,X14) )
      & ( X17 != X12
        | r2_hidden(X17,X15)
        | X15 != k1_enumset1(X12,X13,X14) )
      & ( X17 != X13
        | r2_hidden(X17,X15)
        | X15 != k1_enumset1(X12,X13,X14) )
      & ( X17 != X14
        | r2_hidden(X17,X15)
        | X15 != k1_enumset1(X12,X13,X14) )
      & ( esk2_4(X18,X19,X20,X21) != X18
        | ~ r2_hidden(esk2_4(X18,X19,X20,X21),X21)
        | X21 = k1_enumset1(X18,X19,X20) )
      & ( esk2_4(X18,X19,X20,X21) != X19
        | ~ r2_hidden(esk2_4(X18,X19,X20,X21),X21)
        | X21 = k1_enumset1(X18,X19,X20) )
      & ( esk2_4(X18,X19,X20,X21) != X20
        | ~ r2_hidden(esk2_4(X18,X19,X20,X21),X21)
        | X21 = k1_enumset1(X18,X19,X20) )
      & ( r2_hidden(esk2_4(X18,X19,X20,X21),X21)
        | esk2_4(X18,X19,X20,X21) = X18
        | esk2_4(X18,X19,X20,X21) = X19
        | esk2_4(X18,X19,X20,X21) = X20
        | X21 = k1_enumset1(X18,X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_20,negated_conjecture,
    ( k9_relat_1(esk12_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(esk12_0),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_enumset1(X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( k9_relat_1(esk12_0,X1) = k1_xboole_0
    | r2_hidden(esk1_2(k1_relat_1(esk12_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k9_relat_1(esk12_0,k1_enumset1(X1,X1,X1)) = k11_relat_1(esk12_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_14])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).

cnf(c_0_30,negated_conjecture,
    ( k9_relat_1(esk12_0,X1) = k1_xboole_0
    | r2_hidden(esk1_2(k1_relat_1(esk12_0),X1),k1_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_25])).

cnf(c_0_32,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk11_0,k1_relat_1(esk12_0))
    | k11_relat_1(esk12_0,esk11_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( k11_relat_1(esk12_0,X1) = k1_xboole_0
    | r2_hidden(esk1_2(k1_relat_1(esk12_0),k1_enumset1(X1,X1,X1)),k1_enumset1(X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_2(X1,k1_enumset1(X2,X3,X4)),k1_enumset1(X2,X3,X4))
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( k11_relat_1(esk12_0,X1) = k1_xboole_0
    | r2_hidden(esk1_2(k1_relat_1(esk12_0),k1_enumset1(X1,X1,X1)),k1_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_27])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_2(X1,k1_enumset1(X2,X3,X4)),X1)
    | ~ r2_hidden(X4,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_38,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k1_enumset1(X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(esk12_0),k1_enumset1(esk11_0,esk11_0,esk11_0)),k1_enumset1(esk11_0,esk11_0,esk11_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(esk12_0),k1_enumset1(esk11_0,esk11_0,esk11_0)),k1_relat_1(esk12_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_36]),c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( esk1_2(k1_relat_1(esk12_0),k1_enumset1(esk11_0,esk11_0,esk11_0)) = esk11_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,plain,
    ( r1_xboole_0(k1_relat_1(X1),X2)
    | k9_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_43,negated_conjecture,
    ( k11_relat_1(esk12_0,esk11_0) = k1_xboole_0
    | ~ r2_hidden(esk11_0,k1_relat_1(esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk11_0,k1_relat_1(esk12_0)) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk12_0),k1_enumset1(X1,X1,X1))
    | k11_relat_1(esk12_0,X1) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_27]),c_0_14])])).

cnf(c_0_46,negated_conjecture,
    ( k11_relat_1(esk12_0,esk11_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk12_0),k1_enumset1(esk11_0,esk11_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(X1,k1_enumset1(esk11_0,esk11_0,esk11_0))
    | ~ r2_hidden(X1,k1_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_47])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_44]),c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:25:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 0.12/0.40  # and selection function SelectCQIArEqFirst.
% 0.12/0.40  #
% 0.12/0.40  # Preprocessing time       : 0.029 s
% 0.12/0.40  # Presaturation interreduction done
% 0.12/0.40  
% 0.12/0.40  # Proof found!
% 0.12/0.40  # SZS status Theorem
% 0.12/0.40  # SZS output start CNFRefutation
% 0.12/0.40  fof(t205_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 0.12/0.40  fof(t151_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 0.12/0.40  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 0.12/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.40  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.12/0.40  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.12/0.40  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t205_relat_1])).
% 0.12/0.40  fof(c_0_8, plain, ![X47, X48]:((k9_relat_1(X48,X47)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X48),X47)|~v1_relat_1(X48))&(~r1_xboole_0(k1_relat_1(X48),X47)|k9_relat_1(X48,X47)=k1_xboole_0|~v1_relat_1(X48))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).
% 0.12/0.40  fof(c_0_9, negated_conjecture, (v1_relat_1(esk12_0)&((~r2_hidden(esk11_0,k1_relat_1(esk12_0))|k11_relat_1(esk12_0,esk11_0)=k1_xboole_0)&(r2_hidden(esk11_0,k1_relat_1(esk12_0))|k11_relat_1(esk12_0,esk11_0)!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.12/0.40  fof(c_0_10, plain, ![X26, X27]:(~v1_relat_1(X26)|k11_relat_1(X26,X27)=k9_relat_1(X26,k1_tarski(X27))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.12/0.40  fof(c_0_11, plain, ![X23]:k2_tarski(X23,X23)=k1_tarski(X23), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.40  fof(c_0_12, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.40  cnf(c_0_13, plain, (k9_relat_1(X1,X2)=k1_xboole_0|~r1_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.40  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.40  fof(c_0_15, plain, ![X6, X7, X9, X10, X11]:(((r2_hidden(esk1_2(X6,X7),X6)|r1_xboole_0(X6,X7))&(r2_hidden(esk1_2(X6,X7),X7)|r1_xboole_0(X6,X7)))&(~r2_hidden(X11,X9)|~r2_hidden(X11,X10)|~r1_xboole_0(X9,X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.12/0.40  cnf(c_0_16, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.40  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.40  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.40  fof(c_0_19, plain, ![X12, X13, X14, X15, X16, X17, X18, X19, X20, X21]:(((~r2_hidden(X16,X15)|(X16=X12|X16=X13|X16=X14)|X15!=k1_enumset1(X12,X13,X14))&(((X17!=X12|r2_hidden(X17,X15)|X15!=k1_enumset1(X12,X13,X14))&(X17!=X13|r2_hidden(X17,X15)|X15!=k1_enumset1(X12,X13,X14)))&(X17!=X14|r2_hidden(X17,X15)|X15!=k1_enumset1(X12,X13,X14))))&((((esk2_4(X18,X19,X20,X21)!=X18|~r2_hidden(esk2_4(X18,X19,X20,X21),X21)|X21=k1_enumset1(X18,X19,X20))&(esk2_4(X18,X19,X20,X21)!=X19|~r2_hidden(esk2_4(X18,X19,X20,X21),X21)|X21=k1_enumset1(X18,X19,X20)))&(esk2_4(X18,X19,X20,X21)!=X20|~r2_hidden(esk2_4(X18,X19,X20,X21),X21)|X21=k1_enumset1(X18,X19,X20)))&(r2_hidden(esk2_4(X18,X19,X20,X21),X21)|(esk2_4(X18,X19,X20,X21)=X18|esk2_4(X18,X19,X20,X21)=X19|esk2_4(X18,X19,X20,X21)=X20)|X21=k1_enumset1(X18,X19,X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.19/0.40  cnf(c_0_20, negated_conjecture, (k9_relat_1(esk12_0,X1)=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk12_0),X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.40  cnf(c_0_21, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_22, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_enumset1(X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.19/0.40  cnf(c_0_23, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_24, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_25, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_26, negated_conjecture, (k9_relat_1(esk12_0,X1)=k1_xboole_0|r2_hidden(esk1_2(k1_relat_1(esk12_0),X1),X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.40  cnf(c_0_27, negated_conjecture, (k9_relat_1(esk12_0,k1_enumset1(X1,X1,X1))=k11_relat_1(esk12_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_14])).
% 0.19/0.40  cnf(c_0_28, plain, (r2_hidden(esk1_2(X1,X2),X2)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_23, c_0_21])).
% 0.19/0.40  cnf(c_0_29, plain, (r2_hidden(X1,k1_enumset1(X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).
% 0.19/0.40  cnf(c_0_30, negated_conjecture, (k9_relat_1(esk12_0,X1)=k1_xboole_0|r2_hidden(esk1_2(k1_relat_1(esk12_0),X1),k1_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_20, c_0_25])).
% 0.19/0.40  cnf(c_0_31, plain, (r2_hidden(esk1_2(X1,X2),X1)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_23, c_0_25])).
% 0.19/0.40  cnf(c_0_32, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_33, negated_conjecture, (r2_hidden(esk11_0,k1_relat_1(esk12_0))|k11_relat_1(esk12_0,esk11_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_34, negated_conjecture, (k11_relat_1(esk12_0,X1)=k1_xboole_0|r2_hidden(esk1_2(k1_relat_1(esk12_0),k1_enumset1(X1,X1,X1)),k1_enumset1(X1,X1,X1))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.40  cnf(c_0_35, plain, (r2_hidden(esk1_2(X1,k1_enumset1(X2,X3,X4)),k1_enumset1(X2,X3,X4))|~r2_hidden(X4,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, (k11_relat_1(esk12_0,X1)=k1_xboole_0|r2_hidden(esk1_2(k1_relat_1(esk12_0),k1_enumset1(X1,X1,X1)),k1_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_30, c_0_27])).
% 0.19/0.40  cnf(c_0_37, plain, (r2_hidden(esk1_2(X1,k1_enumset1(X2,X3,X4)),X1)|~r2_hidden(X4,X1)), inference(spm,[status(thm)],[c_0_31, c_0_29])).
% 0.19/0.40  cnf(c_0_38, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k1_enumset1(X4,X3,X2))), inference(er,[status(thm)],[c_0_32])).
% 0.19/0.40  cnf(c_0_39, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(esk12_0),k1_enumset1(esk11_0,esk11_0,esk11_0)),k1_enumset1(esk11_0,esk11_0,esk11_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.19/0.40  cnf(c_0_40, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(esk12_0),k1_enumset1(esk11_0,esk11_0,esk11_0)),k1_relat_1(esk12_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_36]), c_0_37])).
% 0.19/0.40  cnf(c_0_41, negated_conjecture, (esk1_2(k1_relat_1(esk12_0),k1_enumset1(esk11_0,esk11_0,esk11_0))=esk11_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.40  cnf(c_0_42, plain, (r1_xboole_0(k1_relat_1(X1),X2)|k9_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  cnf(c_0_43, negated_conjecture, (k11_relat_1(esk12_0,esk11_0)=k1_xboole_0|~r2_hidden(esk11_0,k1_relat_1(esk12_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_44, negated_conjecture, (r2_hidden(esk11_0,k1_relat_1(esk12_0))), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.40  cnf(c_0_45, negated_conjecture, (r1_xboole_0(k1_relat_1(esk12_0),k1_enumset1(X1,X1,X1))|k11_relat_1(esk12_0,X1)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_27]), c_0_14])])).
% 0.19/0.40  cnf(c_0_46, negated_conjecture, (k11_relat_1(esk12_0,esk11_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])])).
% 0.19/0.40  cnf(c_0_47, negated_conjecture, (r1_xboole_0(k1_relat_1(esk12_0),k1_enumset1(esk11_0,esk11_0,esk11_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.40  cnf(c_0_48, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_49, negated_conjecture, (~r2_hidden(X1,k1_enumset1(esk11_0,esk11_0,esk11_0))|~r2_hidden(X1,k1_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_23, c_0_47])).
% 0.19/0.40  cnf(c_0_50, plain, (r2_hidden(X1,k1_enumset1(X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).
% 0.19/0.40  cnf(c_0_51, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_44]), c_0_50])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 52
% 0.19/0.40  # Proof object clause steps            : 37
% 0.19/0.40  # Proof object formula steps           : 15
% 0.19/0.40  # Proof object conjectures             : 21
% 0.19/0.40  # Proof object clause conjectures      : 18
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 14
% 0.19/0.40  # Proof object initial formulas used   : 7
% 0.19/0.40  # Proof object generating inferences   : 17
% 0.19/0.40  # Proof object simplifying inferences  : 16
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 11
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 29
% 0.19/0.40  # Removed in clause preprocessing      : 2
% 0.19/0.40  # Initial clauses in saturation        : 27
% 0.19/0.40  # Processed clauses                    : 184
% 0.19/0.40  # ...of these trivial                  : 0
% 0.19/0.40  # ...subsumed                          : 25
% 0.19/0.40  # ...remaining for further processing  : 159
% 0.19/0.40  # Other redundant clauses eliminated   : 27
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 0
% 0.19/0.40  # Backward-rewritten                   : 9
% 0.19/0.40  # Generated clauses                    : 1651
% 0.19/0.40  # ...of the previous two non-trivial   : 1514
% 0.19/0.40  # Contextual simplify-reflections      : 2
% 0.19/0.40  # Paramodulations                      : 1621
% 0.19/0.40  # Factorizations                       : 6
% 0.19/0.40  # Equation resolutions                 : 27
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 117
% 0.19/0.40  #    Positive orientable unit clauses  : 25
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 0
% 0.19/0.40  #    Non-unit-clauses                  : 92
% 0.19/0.40  # Current number of unprocessed clauses: 1379
% 0.19/0.40  # ...number of literals in the above   : 3779
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 38
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 923
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 764
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 27
% 0.19/0.40  # Unit Clause-clause subsumption calls : 74
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 45
% 0.19/0.40  # BW rewrite match successes           : 3
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 30688
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.055 s
% 0.19/0.40  # System time              : 0.007 s
% 0.19/0.40  # Total time               : 0.062 s
% 0.19/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
