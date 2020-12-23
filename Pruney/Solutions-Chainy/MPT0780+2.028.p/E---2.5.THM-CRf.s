%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:52 EST 2020

% Result     : Theorem 0.91s
% Output     : CNFRefutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 119 expanded)
%              Number of clauses        :   24 (  54 expanded)
%              Number of leaves         :    7 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :  100 ( 284 expanded)
%              Number of equality atoms :   37 ( 131 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t29_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k2_wellord1(k2_wellord1(X3,X2),X1) = k2_wellord1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

fof(t26_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k2_wellord1(k2_wellord1(X3,X1),X2) = k2_wellord1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

fof(c_0_7,plain,(
    ! [X25,X26] : k1_setfam_1(k2_tarski(X25,X26)) = k3_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_8,plain,(
    ! [X20,X21] : k1_enumset1(X20,X20,X21) = k2_tarski(X20,X21) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_9,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_10,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X22,X23,X24] : k2_enumset1(X22,X22,X23,X24) = k1_enumset1(X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_17,plain,
    ( X3 = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => k2_wellord1(k2_wellord1(X3,X2),X1) = k2_wellord1(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t29_wellord1])).

fof(c_0_19,plain,(
    ! [X27,X28,X29] :
      ( ~ v1_relat_1(X29)
      | k2_wellord1(k2_wellord1(X29,X27),X28) = k2_wellord1(X29,k3_xboole_0(X27,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_wellord1])])).

cnf(c_0_20,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_17])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & r1_tarski(esk3_0,esk4_0)
    & k2_wellord1(k2_wellord1(esk5_0,esk4_0),esk3_0) != k2_wellord1(esk5_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_23,plain,
    ( k2_wellord1(k2_wellord1(X1,X2),X3) = k2_wellord1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k2_wellord1(k2_wellord1(X1,X2),X3) = k2_wellord1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_14]),c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,esk3_0)) = esk3_0
    | r2_hidden(esk2_3(X1,esk3_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,negated_conjecture,
    ( k2_wellord1(k2_wellord1(X1,X2),esk3_0) = k2_wellord1(X1,esk3_0)
    | r2_hidden(esk2_3(X2,esk3_0,esk3_0),esk4_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( X3 = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_14]),c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( k2_wellord1(k2_wellord1(esk5_0,esk4_0),esk3_0) != k2_wellord1(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( k2_wellord1(k2_wellord1(esk5_0,X1),esk3_0) = k2_wellord1(esk5_0,esk3_0)
    | r2_hidden(esk2_3(X1,esk3_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X2
    | ~ r2_hidden(esk2_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_21]),c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,esk3_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_37,negated_conjecture,
    ( k2_wellord1(k2_wellord1(X1,esk4_0),esk3_0) = k2_wellord1(X1,esk3_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_36])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_37]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:01:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.91/1.13  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.91/1.13  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.91/1.13  #
% 0.91/1.13  # Preprocessing time       : 0.027 s
% 0.91/1.13  # Presaturation interreduction done
% 0.91/1.13  
% 0.91/1.13  # Proof found!
% 0.91/1.13  # SZS status Theorem
% 0.91/1.13  # SZS output start CNFRefutation
% 0.91/1.13  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.91/1.13  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.91/1.13  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.91/1.13  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.91/1.13  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.91/1.13  fof(t29_wellord1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k2_wellord1(k2_wellord1(X3,X2),X1)=k2_wellord1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_wellord1)).
% 0.91/1.13  fof(t26_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k2_wellord1(k2_wellord1(X3,X1),X2)=k2_wellord1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_wellord1)).
% 0.91/1.13  fof(c_0_7, plain, ![X25, X26]:k1_setfam_1(k2_tarski(X25,X26))=k3_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.91/1.13  fof(c_0_8, plain, ![X20, X21]:k1_enumset1(X20,X20,X21)=k2_tarski(X20,X21), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.91/1.13  fof(c_0_9, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.91/1.13  cnf(c_0_10, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.91/1.13  cnf(c_0_11, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.91/1.13  fof(c_0_12, plain, ![X22, X23, X24]:k2_enumset1(X22,X22,X23,X24)=k1_enumset1(X22,X23,X24), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.91/1.13  cnf(c_0_13, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.91/1.13  cnf(c_0_14, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.91/1.13  cnf(c_0_15, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.91/1.13  fof(c_0_16, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.91/1.13  cnf(c_0_17, plain, (X3=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.91/1.13  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k2_wellord1(k2_wellord1(X3,X2),X1)=k2_wellord1(X3,X1)))), inference(assume_negation,[status(cth)],[t29_wellord1])).
% 0.91/1.13  fof(c_0_19, plain, ![X27, X28, X29]:(~v1_relat_1(X29)|k2_wellord1(k2_wellord1(X29,X27),X28)=k2_wellord1(X29,k3_xboole_0(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_wellord1])])).
% 0.91/1.13  cnf(c_0_20, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.91/1.13  cnf(c_0_21, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=X2|r2_hidden(esk2_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_17])).
% 0.91/1.13  fof(c_0_22, negated_conjecture, (v1_relat_1(esk5_0)&(r1_tarski(esk3_0,esk4_0)&k2_wellord1(k2_wellord1(esk5_0,esk4_0),esk3_0)!=k2_wellord1(esk5_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.91/1.13  cnf(c_0_23, plain, (k2_wellord1(k2_wellord1(X1,X2),X3)=k2_wellord1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.91/1.13  cnf(c_0_24, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=X2|r2_hidden(esk2_3(X1,X2,X2),X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.91/1.13  cnf(c_0_25, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.91/1.13  cnf(c_0_26, plain, (k2_wellord1(k2_wellord1(X1,X2),X3)=k2_wellord1(X1,k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_14]), c_0_15])).
% 0.91/1.13  cnf(c_0_27, negated_conjecture, (k1_setfam_1(k2_enumset1(X1,X1,X1,esk3_0))=esk3_0|r2_hidden(esk2_3(X1,esk3_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.91/1.13  cnf(c_0_28, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.91/1.13  cnf(c_0_29, negated_conjecture, (k2_wellord1(k2_wellord1(X1,X2),esk3_0)=k2_wellord1(X1,esk3_0)|r2_hidden(esk2_3(X2,esk3_0,esk3_0),esk4_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.91/1.13  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.91/1.13  cnf(c_0_31, plain, (X3=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_14]), c_0_15])).
% 0.91/1.13  cnf(c_0_32, negated_conjecture, (k2_wellord1(k2_wellord1(esk5_0,esk4_0),esk3_0)!=k2_wellord1(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.91/1.13  cnf(c_0_33, negated_conjecture, (k2_wellord1(k2_wellord1(esk5_0,X1),esk3_0)=k2_wellord1(esk5_0,esk3_0)|r2_hidden(esk2_3(X1,esk3_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.91/1.13  cnf(c_0_34, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=X2|~r2_hidden(esk2_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_21]), c_0_21])).
% 0.91/1.13  cnf(c_0_35, negated_conjecture, (r2_hidden(esk2_3(esk4_0,esk3_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.91/1.13  cnf(c_0_36, negated_conjecture, (k1_setfam_1(k2_enumset1(esk4_0,esk4_0,esk4_0,esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.91/1.13  cnf(c_0_37, negated_conjecture, (k2_wellord1(k2_wellord1(X1,esk4_0),esk3_0)=k2_wellord1(X1,esk3_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_36])).
% 0.91/1.13  cnf(c_0_38, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_37]), c_0_30])]), ['proof']).
% 0.91/1.13  # SZS output end CNFRefutation
% 0.91/1.13  # Proof object total steps             : 39
% 0.91/1.13  # Proof object clause steps            : 24
% 0.91/1.13  # Proof object formula steps           : 15
% 0.91/1.13  # Proof object conjectures             : 13
% 0.91/1.13  # Proof object clause conjectures      : 10
% 0.91/1.13  # Proof object formula conjectures     : 3
% 0.91/1.13  # Proof object initial clauses used    : 10
% 0.91/1.13  # Proof object initial formulas used   : 7
% 0.91/1.13  # Proof object generating inferences   : 10
% 0.91/1.13  # Proof object simplifying inferences  : 10
% 0.91/1.13  # Training examples: 0 positive, 0 negative
% 0.91/1.13  # Parsed axioms                        : 7
% 0.91/1.13  # Removed by relevancy pruning/SinE    : 0
% 0.91/1.13  # Initial clauses                      : 16
% 0.91/1.13  # Removed in clause preprocessing      : 3
% 0.91/1.13  # Initial clauses in saturation        : 13
% 0.91/1.13  # Processed clauses                    : 991
% 0.91/1.13  # ...of these trivial                  : 0
% 0.91/1.13  # ...subsumed                          : 548
% 0.91/1.13  # ...remaining for further processing  : 443
% 0.91/1.13  # Other redundant clauses eliminated   : 9
% 0.91/1.13  # Clauses deleted for lack of memory   : 0
% 0.91/1.13  # Backward-subsumed                    : 12
% 0.91/1.13  # Backward-rewritten                   : 24
% 0.91/1.13  # Generated clauses                    : 42903
% 0.91/1.13  # ...of the previous two non-trivial   : 41914
% 0.91/1.13  # Contextual simplify-reflections      : 5
% 0.91/1.13  # Paramodulations                      : 42490
% 0.91/1.13  # Factorizations                       : 404
% 0.91/1.13  # Equation resolutions                 : 9
% 0.91/1.13  # Propositional unsat checks           : 0
% 0.91/1.13  #    Propositional check models        : 0
% 0.91/1.13  #    Propositional check unsatisfiable : 0
% 0.91/1.13  #    Propositional clauses             : 0
% 0.91/1.13  #    Propositional clauses after purity: 0
% 0.91/1.13  #    Propositional unsat core size     : 0
% 0.91/1.13  #    Propositional preprocessing time  : 0.000
% 0.91/1.13  #    Propositional encoding time       : 0.000
% 0.91/1.13  #    Propositional solver time         : 0.000
% 0.91/1.13  #    Success case prop preproc time    : 0.000
% 0.91/1.13  #    Success case prop encoding time   : 0.000
% 0.91/1.13  #    Success case prop solver time     : 0.000
% 0.91/1.13  # Current number of processed clauses  : 391
% 0.91/1.13  #    Positive orientable unit clauses  : 15
% 0.91/1.13  #    Positive unorientable unit clauses: 0
% 0.91/1.13  #    Negative unit clauses             : 1
% 0.91/1.13  #    Non-unit-clauses                  : 375
% 0.91/1.13  # Current number of unprocessed clauses: 40935
% 0.91/1.13  # ...number of literals in the above   : 286310
% 0.91/1.13  # Current number of archived formulas  : 0
% 0.91/1.13  # Current number of archived clauses   : 52
% 0.91/1.13  # Clause-clause subsumption calls (NU) : 38863
% 0.91/1.13  # Rec. Clause-clause subsumption calls : 9691
% 0.91/1.13  # Non-unit clause-clause subsumptions  : 565
% 0.91/1.13  # Unit Clause-clause subsumption calls : 546
% 0.91/1.13  # Rewrite failures with RHS unbound    : 0
% 0.91/1.13  # BW rewrite match attempts            : 79
% 0.91/1.13  # BW rewrite match successes           : 1
% 0.91/1.13  # Condensation attempts                : 0
% 0.91/1.13  # Condensation successes               : 0
% 0.91/1.13  # Termbank termtop insertions          : 1383719
% 0.91/1.13  
% 0.91/1.13  # -------------------------------------------------
% 0.91/1.13  # User time                : 0.756 s
% 0.91/1.13  # System time              : 0.019 s
% 0.91/1.13  # Total time               : 0.774 s
% 0.91/1.13  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
