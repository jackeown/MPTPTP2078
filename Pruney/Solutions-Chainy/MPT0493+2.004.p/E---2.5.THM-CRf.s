%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:30 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 117 expanded)
%              Number of clauses        :   27 (  54 expanded)
%              Number of leaves         :    8 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  101 ( 257 expanded)
%              Number of equality atoms :   39 ( 123 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t91_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(c_0_8,plain,(
    ! [X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_9,plain,(
    ! [X25,X26] : k1_setfam_1(k2_tarski(X25,X26)) = k3_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_10,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k4_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X20] : k4_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X1) = k1_setfam_1(k2_tarski(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_19,plain,(
    ! [X23,X24] : k2_tarski(X23,X24) = k2_tarski(X24,X23) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X2,k1_xboole_0)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_22,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X28)
      | k1_relat_1(k7_relat_1(X28,X27)) = k3_xboole_0(k1_relat_1(X28),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_15])).

cnf(c_0_24,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_25,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_16]),c_0_16])])).

cnf(c_0_27,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k1_relat_1(X2))
         => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t91_relat_1])).

cnf(c_0_29,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_24,c_0_12])).

cnf(c_0_30,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_32,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & r1_tarski(esk3_0,k1_relat_1(esk4_0))
    & k1_relat_1(k7_relat_1(esk4_0,esk3_0)) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

cnf(c_0_33,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_relat_1(X2))) = k1_relat_1(k7_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_21])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk2_3(X1,X2,k1_xboole_0),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,esk3_0)) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_relat_1(X2))) = k1_relat_1(k7_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_40,negated_conjecture,
    ( k4_xboole_0(esk3_0,X1) = k1_xboole_0
    | r2_hidden(esk2_3(esk3_0,X1,k1_xboole_0),k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k1_relat_1(esk4_0))) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(esk3_0,k1_relat_1(esk4_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_26])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.45  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.45  #
% 0.19/0.45  # Preprocessing time       : 0.027 s
% 0.19/0.45  # Presaturation interreduction done
% 0.19/0.45  
% 0.19/0.45  # Proof found!
% 0.19/0.45  # SZS status Theorem
% 0.19/0.45  # SZS output start CNFRefutation
% 0.19/0.45  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.45  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.45  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.45  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.45  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.45  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 0.19/0.45  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.45  fof(t91_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 0.19/0.45  fof(c_0_8, plain, ![X21, X22]:k4_xboole_0(X21,k4_xboole_0(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.45  fof(c_0_9, plain, ![X25, X26]:k1_setfam_1(k2_tarski(X25,X26))=k3_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.45  fof(c_0_10, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.45  cnf(c_0_11, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.45  cnf(c_0_12, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.45  fof(c_0_13, plain, ![X20]:k4_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.45  cnf(c_0_14, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.45  cnf(c_0_15, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_tarski(X1,X2))), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.45  cnf(c_0_16, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.45  cnf(c_0_17, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_14])).
% 0.19/0.45  cnf(c_0_18, plain, (k4_xboole_0(X1,X1)=k1_setfam_1(k2_tarski(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.45  fof(c_0_19, plain, ![X23, X24]:k2_tarski(X23,X24)=k2_tarski(X24,X23), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.45  cnf(c_0_20, plain, (~r2_hidden(X1,k1_setfam_1(k2_tarski(X2,k1_xboole_0)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.45  cnf(c_0_21, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.45  fof(c_0_22, plain, ![X27, X28]:(~v1_relat_1(X28)|k1_relat_1(k7_relat_1(X28,X27))=k3_xboole_0(k1_relat_1(X28),X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.19/0.45  cnf(c_0_23, plain, (~r2_hidden(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_15])).
% 0.19/0.45  cnf(c_0_24, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.45  fof(c_0_25, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.45  cnf(c_0_26, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_16]), c_0_16])])).
% 0.19/0.45  cnf(c_0_27, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.45  fof(c_0_28, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1))), inference(assume_negation,[status(cth)],[t91_relat_1])).
% 0.19/0.45  cnf(c_0_29, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k2_tarski(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_24, c_0_12])).
% 0.19/0.45  cnf(c_0_30, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.45  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk2_3(X1,X2,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.45  fof(c_0_32, negated_conjecture, (v1_relat_1(esk4_0)&(r1_tarski(esk3_0,k1_relat_1(esk4_0))&k1_relat_1(k7_relat_1(esk4_0,esk3_0))!=esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 0.19/0.45  cnf(c_0_33, plain, (k1_setfam_1(k2_tarski(X1,k1_relat_1(X2)))=k1_relat_1(k7_relat_1(X2,X1))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_29, c_0_21])).
% 0.19/0.45  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk2_3(X1,X2,k1_xboole_0),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.45  cnf(c_0_35, negated_conjecture, (r1_tarski(esk3_0,k1_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.45  cnf(c_0_36, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,esk3_0))!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.45  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_relat_1(X2)))=k1_relat_1(k7_relat_1(X2,X1))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_33, c_0_15])).
% 0.19/0.45  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.45  cnf(c_0_39, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.45  cnf(c_0_40, negated_conjecture, (k4_xboole_0(esk3_0,X1)=k1_xboole_0|r2_hidden(esk2_3(esk3_0,X1,k1_xboole_0),k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.45  cnf(c_0_41, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k1_relat_1(esk4_0)))!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.19/0.45  cnf(c_0_42, negated_conjecture, (k4_xboole_0(esk3_0,k1_relat_1(esk4_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_26])).
% 0.19/0.45  cnf(c_0_43, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_16])]), ['proof']).
% 0.19/0.45  # SZS output end CNFRefutation
% 0.19/0.45  # Proof object total steps             : 44
% 0.19/0.45  # Proof object clause steps            : 27
% 0.19/0.45  # Proof object formula steps           : 17
% 0.19/0.45  # Proof object conjectures             : 10
% 0.19/0.45  # Proof object clause conjectures      : 7
% 0.19/0.45  # Proof object formula conjectures     : 3
% 0.19/0.45  # Proof object initial clauses used    : 12
% 0.19/0.45  # Proof object initial formulas used   : 8
% 0.19/0.45  # Proof object generating inferences   : 11
% 0.19/0.45  # Proof object simplifying inferences  : 12
% 0.19/0.45  # Training examples: 0 positive, 0 negative
% 0.19/0.45  # Parsed axioms                        : 8
% 0.19/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.45  # Initial clauses                      : 17
% 0.19/0.45  # Removed in clause preprocessing      : 1
% 0.19/0.45  # Initial clauses in saturation        : 16
% 0.19/0.45  # Processed clauses                    : 838
% 0.19/0.45  # ...of these trivial                  : 16
% 0.19/0.45  # ...subsumed                          : 588
% 0.19/0.45  # ...remaining for further processing  : 234
% 0.19/0.45  # Other redundant clauses eliminated   : 3
% 0.19/0.45  # Clauses deleted for lack of memory   : 0
% 0.19/0.45  # Backward-subsumed                    : 8
% 0.19/0.45  # Backward-rewritten                   : 28
% 0.19/0.45  # Generated clauses                    : 3735
% 0.19/0.45  # ...of the previous two non-trivial   : 3273
% 0.19/0.45  # Contextual simplify-reflections      : 1
% 0.19/0.45  # Paramodulations                      : 3722
% 0.19/0.45  # Factorizations                       : 10
% 0.19/0.45  # Equation resolutions                 : 3
% 0.19/0.45  # Propositional unsat checks           : 0
% 0.19/0.45  #    Propositional check models        : 0
% 0.19/0.45  #    Propositional check unsatisfiable : 0
% 0.19/0.45  #    Propositional clauses             : 0
% 0.19/0.45  #    Propositional clauses after purity: 0
% 0.19/0.45  #    Propositional unsat core size     : 0
% 0.19/0.45  #    Propositional preprocessing time  : 0.000
% 0.19/0.45  #    Propositional encoding time       : 0.000
% 0.19/0.45  #    Propositional solver time         : 0.000
% 0.19/0.45  #    Success case prop preproc time    : 0.000
% 0.19/0.45  #    Success case prop encoding time   : 0.000
% 0.19/0.45  #    Success case prop solver time     : 0.000
% 0.19/0.45  # Current number of processed clauses  : 179
% 0.19/0.45  #    Positive orientable unit clauses  : 23
% 0.19/0.45  #    Positive unorientable unit clauses: 3
% 0.19/0.45  #    Negative unit clauses             : 2
% 0.19/0.45  #    Non-unit-clauses                  : 151
% 0.19/0.45  # Current number of unprocessed clauses: 2396
% 0.19/0.45  # ...number of literals in the above   : 8742
% 0.19/0.45  # Current number of archived formulas  : 0
% 0.19/0.45  # Current number of archived clauses   : 53
% 0.19/0.45  # Clause-clause subsumption calls (NU) : 4260
% 0.19/0.45  # Rec. Clause-clause subsumption calls : 3086
% 0.19/0.45  # Non-unit clause-clause subsumptions  : 391
% 0.19/0.45  # Unit Clause-clause subsumption calls : 80
% 0.19/0.45  # Rewrite failures with RHS unbound    : 0
% 0.19/0.45  # BW rewrite match attempts            : 121
% 0.19/0.45  # BW rewrite match successes           : 41
% 0.19/0.45  # Condensation attempts                : 0
% 0.19/0.45  # Condensation successes               : 0
% 0.19/0.45  # Termbank termtop insertions          : 62400
% 0.19/0.45  
% 0.19/0.45  # -------------------------------------------------
% 0.19/0.45  # User time                : 0.097 s
% 0.19/0.45  # System time              : 0.008 s
% 0.19/0.45  # Total time               : 0.105 s
% 0.19/0.45  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
