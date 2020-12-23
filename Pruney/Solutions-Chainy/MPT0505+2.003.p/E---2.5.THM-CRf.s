%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:45 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 105 expanded)
%              Number of clauses        :   26 (  49 expanded)
%              Number of leaves         :    6 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  103 ( 287 expanded)
%              Number of equality atoms :   37 ( 116 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t103_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X2),X1) = k7_relat_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_6,plain,(
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

fof(c_0_7,plain,(
    ! [X22,X23] : k1_setfam_1(k2_tarski(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_8,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_11,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => k7_relat_1(k7_relat_1(X3,X2),X1) = k7_relat_1(X3,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t103_relat_1])).

fof(c_0_13,plain,(
    ! [X24,X25,X26] :
      ( ~ v1_relat_1(X26)
      | k7_relat_1(k7_relat_1(X26,X24),X25) = k7_relat_1(X26,k3_xboole_0(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

cnf(c_0_14,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_11])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & r1_tarski(esk3_0,esk4_0)
    & k7_relat_1(k7_relat_1(esk5_0,esk4_0),esk3_0) != k7_relat_1(esk5_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_17,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_17,c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,esk3_0)) = esk3_0
    | r2_hidden(esk2_3(X1,esk3_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_23,plain,(
    ! [X20,X21] : k2_tarski(X20,X21) = k2_tarski(X21,X20) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_24,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_20,c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,X2),esk3_0) = k7_relat_1(X1,esk3_0)
    | r2_hidden(esk2_3(X2,esk3_0,esk3_0),esk4_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ r2_hidden(esk2_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_15]),c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk5_0,esk4_0),esk3_0) != k7_relat_1(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk5_0,X1),esk3_0) = k7_relat_1(esk5_0,esk3_0)
    | r2_hidden(esk2_3(X1,esk3_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( k7_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3))) = k7_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_27])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r2_hidden(esk2_3(X2,X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk2_3(esk4_0,esk3_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk3_0,esk4_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk5_0,esk3_0),esk4_0) != k7_relat_1(esk5_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_34]),c_0_26])])).

cnf(c_0_37,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,esk3_0),esk4_0) = k7_relat_1(X1,esk3_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.46/0.64  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.46/0.64  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.46/0.64  #
% 0.46/0.64  # Preprocessing time       : 0.016 s
% 0.46/0.64  # Presaturation interreduction done
% 0.46/0.64  
% 0.46/0.64  # Proof found!
% 0.46/0.64  # SZS status Theorem
% 0.46/0.64  # SZS output start CNFRefutation
% 0.46/0.64  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.46/0.64  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.46/0.64  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.46/0.64  fof(t103_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k7_relat_1(X3,X2),X1)=k7_relat_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 0.46/0.64  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 0.46/0.64  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.46/0.64  fof(c_0_6, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.46/0.64  fof(c_0_7, plain, ![X22, X23]:k1_setfam_1(k2_tarski(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.46/0.64  cnf(c_0_8, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.46/0.64  cnf(c_0_9, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.46/0.64  fof(c_0_10, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.46/0.64  cnf(c_0_11, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_8, c_0_9])).
% 0.46/0.64  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k7_relat_1(X3,X2),X1)=k7_relat_1(X3,X1)))), inference(assume_negation,[status(cth)],[t103_relat_1])).
% 0.46/0.64  fof(c_0_13, plain, ![X24, X25, X26]:(~v1_relat_1(X26)|k7_relat_1(k7_relat_1(X26,X24),X25)=k7_relat_1(X26,k3_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.46/0.64  cnf(c_0_14, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.46/0.64  cnf(c_0_15, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|r2_hidden(esk2_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_11])).
% 0.46/0.64  fof(c_0_16, negated_conjecture, (v1_relat_1(esk5_0)&(r1_tarski(esk3_0,esk4_0)&k7_relat_1(k7_relat_1(esk5_0,esk4_0),esk3_0)!=k7_relat_1(esk5_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.46/0.64  cnf(c_0_17, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.46/0.64  cnf(c_0_18, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|r2_hidden(esk2_3(X1,X2,X2),X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.46/0.64  cnf(c_0_19, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.46/0.64  cnf(c_0_20, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.46/0.64  cnf(c_0_21, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_17, c_0_9])).
% 0.46/0.64  cnf(c_0_22, negated_conjecture, (k1_setfam_1(k2_tarski(X1,esk3_0))=esk3_0|r2_hidden(esk2_3(X1,esk3_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.46/0.64  fof(c_0_23, plain, ![X20, X21]:k2_tarski(X20,X21)=k2_tarski(X21,X20), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.46/0.64  cnf(c_0_24, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_20, c_0_9])).
% 0.46/0.64  cnf(c_0_25, negated_conjecture, (k7_relat_1(k7_relat_1(X1,X2),esk3_0)=k7_relat_1(X1,esk3_0)|r2_hidden(esk2_3(X2,esk3_0,esk3_0),esk4_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.46/0.64  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.46/0.64  cnf(c_0_27, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.46/0.64  cnf(c_0_28, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~r2_hidden(esk2_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_15]), c_0_15])).
% 0.46/0.64  cnf(c_0_29, negated_conjecture, (k7_relat_1(k7_relat_1(esk5_0,esk4_0),esk3_0)!=k7_relat_1(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.46/0.64  cnf(c_0_30, negated_conjecture, (k7_relat_1(k7_relat_1(esk5_0,X1),esk3_0)=k7_relat_1(esk5_0,esk3_0)|r2_hidden(esk2_3(X1,esk3_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.46/0.64  cnf(c_0_31, plain, (k7_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3)))=k7_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_27])).
% 0.46/0.64  cnf(c_0_32, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r2_hidden(esk2_3(X2,X1,X1),X2)), inference(spm,[status(thm)],[c_0_28, c_0_27])).
% 0.46/0.64  cnf(c_0_33, negated_conjecture, (r2_hidden(esk2_3(esk4_0,esk3_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.46/0.64  cnf(c_0_34, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_31])).
% 0.46/0.64  cnf(c_0_35, negated_conjecture, (k1_setfam_1(k2_tarski(esk3_0,esk4_0))=esk3_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.46/0.64  cnf(c_0_36, negated_conjecture, (k7_relat_1(k7_relat_1(esk5_0,esk3_0),esk4_0)!=k7_relat_1(esk5_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_34]), c_0_26])])).
% 0.46/0.64  cnf(c_0_37, negated_conjecture, (k7_relat_1(k7_relat_1(X1,esk3_0),esk4_0)=k7_relat_1(X1,esk3_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_35])).
% 0.46/0.64  cnf(c_0_38, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_26])]), ['proof']).
% 0.46/0.64  # SZS output end CNFRefutation
% 0.46/0.64  # Proof object total steps             : 39
% 0.46/0.64  # Proof object clause steps            : 26
% 0.46/0.64  # Proof object formula steps           : 13
% 0.46/0.64  # Proof object conjectures             : 14
% 0.46/0.64  # Proof object clause conjectures      : 11
% 0.46/0.64  # Proof object formula conjectures     : 3
% 0.46/0.64  # Proof object initial clauses used    : 9
% 0.46/0.64  # Proof object initial formulas used   : 6
% 0.46/0.64  # Proof object generating inferences   : 14
% 0.46/0.64  # Proof object simplifying inferences  : 8
% 0.46/0.64  # Training examples: 0 positive, 0 negative
% 0.46/0.64  # Parsed axioms                        : 6
% 0.46/0.64  # Removed by relevancy pruning/SinE    : 0
% 0.46/0.64  # Initial clauses                      : 15
% 0.46/0.64  # Removed in clause preprocessing      : 1
% 0.46/0.64  # Initial clauses in saturation        : 14
% 0.46/0.64  # Processed clauses                    : 1268
% 0.46/0.64  # ...of these trivial                  : 20
% 0.46/0.64  # ...subsumed                          : 887
% 0.46/0.64  # ...remaining for further processing  : 361
% 0.46/0.64  # Other redundant clauses eliminated   : 15
% 0.46/0.64  # Clauses deleted for lack of memory   : 0
% 0.46/0.64  # Backward-subsumed                    : 10
% 0.46/0.64  # Backward-rewritten                   : 53
% 0.46/0.64  # Generated clauses                    : 20841
% 0.46/0.64  # ...of the previous two non-trivial   : 19964
% 0.46/0.64  # Contextual simplify-reflections      : 3
% 0.46/0.64  # Paramodulations                      : 20582
% 0.46/0.64  # Factorizations                       : 244
% 0.46/0.64  # Equation resolutions                 : 15
% 0.46/0.64  # Propositional unsat checks           : 0
% 0.46/0.64  #    Propositional check models        : 0
% 0.46/0.64  #    Propositional check unsatisfiable : 0
% 0.46/0.64  #    Propositional clauses             : 0
% 0.46/0.64  #    Propositional clauses after purity: 0
% 0.46/0.64  #    Propositional unsat core size     : 0
% 0.46/0.64  #    Propositional preprocessing time  : 0.000
% 0.46/0.64  #    Propositional encoding time       : 0.000
% 0.46/0.64  #    Propositional solver time         : 0.000
% 0.46/0.64  #    Success case prop preproc time    : 0.000
% 0.46/0.64  #    Success case prop encoding time   : 0.000
% 0.46/0.64  #    Success case prop solver time     : 0.000
% 0.46/0.64  # Current number of processed clauses  : 281
% 0.46/0.64  #    Positive orientable unit clauses  : 18
% 0.46/0.64  #    Positive unorientable unit clauses: 1
% 0.46/0.64  #    Negative unit clauses             : 2
% 0.46/0.64  #    Non-unit-clauses                  : 260
% 0.46/0.64  # Current number of unprocessed clauses: 18598
% 0.46/0.64  # ...number of literals in the above   : 100403
% 0.46/0.64  # Current number of archived formulas  : 0
% 0.46/0.64  # Current number of archived clauses   : 78
% 0.46/0.64  # Clause-clause subsumption calls (NU) : 31718
% 0.46/0.64  # Rec. Clause-clause subsumption calls : 8432
% 0.46/0.64  # Non-unit clause-clause subsumptions  : 899
% 0.46/0.64  # Unit Clause-clause subsumption calls : 455
% 0.46/0.64  # Rewrite failures with RHS unbound    : 0
% 0.46/0.64  # BW rewrite match attempts            : 136
% 0.46/0.64  # BW rewrite match successes           : 8
% 0.46/0.64  # Condensation attempts                : 0
% 0.46/0.64  # Condensation successes               : 0
% 0.46/0.64  # Termbank termtop insertions          : 492338
% 0.46/0.64  
% 0.46/0.64  # -------------------------------------------------
% 0.46/0.64  # User time                : 0.291 s
% 0.46/0.64  # System time              : 0.010 s
% 0.46/0.64  # Total time               : 0.301 s
% 0.46/0.64  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
