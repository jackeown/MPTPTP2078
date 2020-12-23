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
% DateTime   : Thu Dec  3 10:34:44 EST 2020

% Result     : Theorem 0.59s
% Output     : CNFRefutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   42 (  66 expanded)
%              Number of clauses        :   25 (  31 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :  114 ( 169 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t106_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_8,plain,(
    ! [X26,X27,X28] :
      ( ( r1_xboole_0(X26,k2_xboole_0(X27,X28))
        | ~ r1_xboole_0(X26,X27)
        | ~ r1_xboole_0(X26,X28) )
      & ( r1_xboole_0(X26,X27)
        | ~ r1_xboole_0(X26,k2_xboole_0(X27,X28)) )
      & ( r1_xboole_0(X26,X28)
        | ~ r1_xboole_0(X26,k2_xboole_0(X27,X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

fof(c_0_9,plain,(
    ! [X20,X21] :
      ( ~ r1_xboole_0(X20,X21)
      | r1_xboole_0(X21,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_10,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | k2_xboole_0(X24,X25) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_13,plain,(
    ! [X29,X30] : r1_xboole_0(k4_xboole_0(X29,X30),X30) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_14,plain,(
    ! [X22,X23] : k4_xboole_0(X22,X23) = k5_xboole_0(X22,k3_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k4_xboole_0(X2,X3))
       => ( r1_tarski(X1,X2)
          & r1_xboole_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t106_xboole_1])).

cnf(c_0_16,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(k2_xboole_0(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,negated_conjecture,
    ( r1_tarski(esk3_0,k4_xboole_0(esk4_0,esk5_0))
    & ( ~ r1_tarski(esk3_0,esk4_0)
      | ~ r1_xboole_0(esk3_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_21,plain,(
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

fof(c_0_22,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_23,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X3,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk3_0,k4_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X2,k5_xboole_0(X3,k3_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_19])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_26,c_0_19])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0)))
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0)
    | ~ r1_xboole_0(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_33])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),esk4_0)
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.59/0.77  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S0U
% 0.59/0.77  # and selection function SelectComplexExceptRRHorn.
% 0.59/0.77  #
% 0.59/0.77  # Preprocessing time       : 0.044 s
% 0.59/0.77  # Presaturation interreduction done
% 0.59/0.77  
% 0.59/0.77  # Proof found!
% 0.59/0.77  # SZS status Theorem
% 0.59/0.77  # SZS output start CNFRefutation
% 0.59/0.77  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.59/0.77  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.59/0.77  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.59/0.77  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.59/0.77  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.59/0.77  fof(t106_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.59/0.77  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.59/0.77  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.59/0.77  fof(c_0_8, plain, ![X26, X27, X28]:((r1_xboole_0(X26,k2_xboole_0(X27,X28))|~r1_xboole_0(X26,X27)|~r1_xboole_0(X26,X28))&((r1_xboole_0(X26,X27)|~r1_xboole_0(X26,k2_xboole_0(X27,X28)))&(r1_xboole_0(X26,X28)|~r1_xboole_0(X26,k2_xboole_0(X27,X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.59/0.77  fof(c_0_9, plain, ![X20, X21]:(~r1_xboole_0(X20,X21)|r1_xboole_0(X21,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.59/0.77  cnf(c_0_10, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.59/0.77  cnf(c_0_11, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.59/0.77  fof(c_0_12, plain, ![X24, X25]:(~r1_tarski(X24,X25)|k2_xboole_0(X24,X25)=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.59/0.77  fof(c_0_13, plain, ![X29, X30]:r1_xboole_0(k4_xboole_0(X29,X30),X30), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.59/0.77  fof(c_0_14, plain, ![X22, X23]:k4_xboole_0(X22,X23)=k5_xboole_0(X22,k3_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.59/0.77  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t106_xboole_1])).
% 0.59/0.77  cnf(c_0_16, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(k2_xboole_0(X2,X3),X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.59/0.77  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.59/0.77  cnf(c_0_18, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.59/0.77  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.59/0.77  fof(c_0_20, negated_conjecture, (r1_tarski(esk3_0,k4_xboole_0(esk4_0,esk5_0))&(~r1_tarski(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.59/0.77  fof(c_0_21, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.59/0.77  fof(c_0_22, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.59/0.77  cnf(c_0_23, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X3,X1)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.59/0.77  cnf(c_0_24, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.59/0.77  cnf(c_0_25, negated_conjecture, (r1_tarski(esk3_0,k4_xboole_0(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.59/0.77  cnf(c_0_26, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.59/0.77  cnf(c_0_27, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.59/0.77  cnf(c_0_28, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.59/0.77  cnf(c_0_29, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X2,k5_xboole_0(X3,k3_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.59/0.77  cnf(c_0_30, negated_conjecture, (r1_tarski(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0)))), inference(rw,[status(thm)],[c_0_25, c_0_19])).
% 0.59/0.77  cnf(c_0_31, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_26, c_0_19])).
% 0.59/0.77  cnf(c_0_32, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.59/0.77  cnf(c_0_33, negated_conjecture, (r1_xboole_0(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.59/0.77  cnf(c_0_34, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_31])).
% 0.59/0.77  cnf(c_0_35, negated_conjecture, (r2_hidden(esk1_2(esk3_0,X1),k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0)))|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_32, c_0_30])).
% 0.59/0.77  cnf(c_0_36, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.59/0.77  cnf(c_0_37, negated_conjecture, (r1_xboole_0(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_11, c_0_33])).
% 0.59/0.77  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.59/0.77  cnf(c_0_39, negated_conjecture, (r2_hidden(esk1_2(esk3_0,X1),esk4_0)|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.59/0.77  cnf(c_0_40, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37])])).
% 0.59/0.77  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), ['proof']).
% 0.59/0.77  # SZS output end CNFRefutation
% 0.59/0.77  # Proof object total steps             : 42
% 0.59/0.77  # Proof object clause steps            : 25
% 0.59/0.77  # Proof object formula steps           : 17
% 0.59/0.77  # Proof object conjectures             : 12
% 0.59/0.77  # Proof object clause conjectures      : 9
% 0.59/0.77  # Proof object formula conjectures     : 3
% 0.59/0.77  # Proof object initial clauses used    : 11
% 0.59/0.77  # Proof object initial formulas used   : 8
% 0.59/0.77  # Proof object generating inferences   : 9
% 0.59/0.77  # Proof object simplifying inferences  : 7
% 0.59/0.77  # Training examples: 0 positive, 0 negative
% 0.59/0.77  # Parsed axioms                        : 8
% 0.59/0.77  # Removed by relevancy pruning/SinE    : 0
% 0.59/0.77  # Initial clauses                      : 18
% 0.59/0.77  # Removed in clause preprocessing      : 1
% 0.59/0.77  # Initial clauses in saturation        : 17
% 0.59/0.77  # Processed clauses                    : 1558
% 0.59/0.77  # ...of these trivial                  : 23
% 0.59/0.77  # ...subsumed                          : 925
% 0.59/0.77  # ...remaining for further processing  : 610
% 0.59/0.77  # Other redundant clauses eliminated   : 3
% 0.59/0.77  # Clauses deleted for lack of memory   : 0
% 0.59/0.77  # Backward-subsumed                    : 34
% 0.59/0.77  # Backward-rewritten                   : 7
% 0.59/0.77  # Generated clauses                    : 15847
% 0.59/0.77  # ...of the previous two non-trivial   : 14930
% 0.59/0.77  # Contextual simplify-reflections      : 2
% 0.59/0.77  # Paramodulations                      : 15752
% 0.59/0.77  # Factorizations                       : 92
% 0.59/0.77  # Equation resolutions                 : 3
% 0.59/0.77  # Propositional unsat checks           : 0
% 0.59/0.77  #    Propositional check models        : 0
% 0.59/0.77  #    Propositional check unsatisfiable : 0
% 0.59/0.77  #    Propositional clauses             : 0
% 0.59/0.77  #    Propositional clauses after purity: 0
% 0.59/0.77  #    Propositional unsat core size     : 0
% 0.59/0.77  #    Propositional preprocessing time  : 0.000
% 0.59/0.77  #    Propositional encoding time       : 0.000
% 0.59/0.77  #    Propositional solver time         : 0.000
% 0.59/0.77  #    Success case prop preproc time    : 0.000
% 0.59/0.77  #    Success case prop encoding time   : 0.000
% 0.59/0.77  #    Success case prop solver time     : 0.000
% 0.59/0.77  # Current number of processed clauses  : 549
% 0.59/0.77  #    Positive orientable unit clauses  : 49
% 0.59/0.77  #    Positive unorientable unit clauses: 0
% 0.59/0.77  #    Negative unit clauses             : 5
% 0.59/0.77  #    Non-unit-clauses                  : 495
% 0.59/0.77  # Current number of unprocessed clauses: 13307
% 0.59/0.77  # ...number of literals in the above   : 60359
% 0.59/0.77  # Current number of archived formulas  : 0
% 0.59/0.77  # Current number of archived clauses   : 59
% 0.59/0.77  # Clause-clause subsumption calls (NU) : 35466
% 0.59/0.77  # Rec. Clause-clause subsumption calls : 26267
% 0.59/0.77  # Non-unit clause-clause subsumptions  : 879
% 0.59/0.77  # Unit Clause-clause subsumption calls : 550
% 0.59/0.77  # Rewrite failures with RHS unbound    : 0
% 0.59/0.77  # BW rewrite match attempts            : 114
% 0.59/0.77  # BW rewrite match successes           : 7
% 0.59/0.77  # Condensation attempts                : 0
% 0.59/0.77  # Condensation successes               : 0
% 0.59/0.77  # Termbank termtop insertions          : 285550
% 0.59/0.78  
% 0.59/0.78  # -------------------------------------------------
% 0.59/0.78  # User time                : 0.422 s
% 0.59/0.78  # System time              : 0.013 s
% 0.59/0.78  # Total time               : 0.435 s
% 0.59/0.78  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
