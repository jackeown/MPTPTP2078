%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:49 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 (  86 expanded)
%              Number of clauses        :   26 (  38 expanded)
%              Number of leaves         :    6 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  108 ( 273 expanded)
%              Number of equality atoms :   22 (  70 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t14_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2)
        & ! [X4] :
            ( ( r1_tarski(X1,X4)
              & r1_tarski(X3,X4) )
           => r1_tarski(X2,X4) ) )
     => X2 = k2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X2)
          & ! [X4] :
              ( ( r1_tarski(X1,X4)
                & r1_tarski(X3,X4) )
             => r1_tarski(X2,X4) ) )
       => X2 = k2_xboole_0(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t14_xboole_1])).

fof(c_0_7,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X16,X15)
        | r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | r2_hidden(X17,X15)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k2_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k2_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X20)
        | r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k2_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_8,plain,(
    ! [X22,X23] :
      ( ~ r1_tarski(X22,X23)
      | k2_xboole_0(X22,X23) = X23 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_9,negated_conjecture,(
    ! [X29] :
      ( r1_tarski(esk3_0,esk4_0)
      & r1_tarski(esk5_0,esk4_0)
      & ( ~ r1_tarski(esk3_0,X29)
        | ~ r1_tarski(esk5_0,X29)
        | r1_tarski(esk4_0,X29) )
      & esk4_0 != k2_xboole_0(esk3_0,esk5_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

fof(c_0_10,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_11,plain,(
    ! [X24,X25] : r1_tarski(X24,k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_12,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_tarski(esk3_0,X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk5_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk4_0,k2_xboole_0(esk5_0,X1))
    | ~ r1_tarski(esk3_0,k2_xboole_0(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk3_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_22]),c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X2)
    | r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X1)
    | r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk4_0,k2_xboole_0(X1,esk5_0))
    | ~ r1_tarski(esk3_0,k2_xboole_0(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r2_hidden(esk1_2(X1,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_2(k2_xboole_0(esk5_0,X1),X2),esk4_0)
    | r2_hidden(esk1_2(k2_xboole_0(esk5_0,X1),X2),X1)
    | r1_tarski(k2_xboole_0(esk5_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk4_0,k2_xboole_0(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_16]),c_0_16]),c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk5_0)) = k2_xboole_0(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( esk4_0 != k2_xboole_0(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_35]),c_0_16]),c_0_36]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.52  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.19/0.52  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.52  #
% 0.19/0.52  # Preprocessing time       : 0.027 s
% 0.19/0.52  # Presaturation interreduction done
% 0.19/0.52  
% 0.19/0.52  # Proof found!
% 0.19/0.52  # SZS status Theorem
% 0.19/0.52  # SZS output start CNFRefutation
% 0.19/0.52  fof(t14_xboole_1, conjecture, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X3,X2))&![X4]:((r1_tarski(X1,X4)&r1_tarski(X3,X4))=>r1_tarski(X2,X4)))=>X2=k2_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_xboole_1)).
% 0.19/0.52  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.19/0.52  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.52  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.52  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.52  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.52  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X3,X2))&![X4]:((r1_tarski(X1,X4)&r1_tarski(X3,X4))=>r1_tarski(X2,X4)))=>X2=k2_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t14_xboole_1])).
% 0.19/0.52  fof(c_0_7, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X16,X15)|(r2_hidden(X16,X13)|r2_hidden(X16,X14))|X15!=k2_xboole_0(X13,X14))&((~r2_hidden(X17,X13)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))&(~r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))))&(((~r2_hidden(esk2_3(X18,X19,X20),X18)|~r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|~r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19)))&(r2_hidden(esk2_3(X18,X19,X20),X20)|(r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k2_xboole_0(X18,X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.19/0.52  fof(c_0_8, plain, ![X22, X23]:(~r1_tarski(X22,X23)|k2_xboole_0(X22,X23)=X23), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.52  fof(c_0_9, negated_conjecture, ![X29]:(((r1_tarski(esk3_0,esk4_0)&r1_tarski(esk5_0,esk4_0))&(~r1_tarski(esk3_0,X29)|~r1_tarski(esk5_0,X29)|r1_tarski(esk4_0,X29)))&esk4_0!=k2_xboole_0(esk3_0,esk5_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).
% 0.19/0.52  fof(c_0_10, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.52  fof(c_0_11, plain, ![X24, X25]:r1_tarski(X24,k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.52  fof(c_0_12, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.52  cnf(c_0_13, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.52  cnf(c_0_14, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.52  cnf(c_0_15, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.52  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.52  cnf(c_0_17, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.52  cnf(c_0_18, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_tarski(esk3_0,X1)|~r1_tarski(esk5_0,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.52  cnf(c_0_19, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.52  cnf(c_0_20, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.52  cnf(c_0_21, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_13])).
% 0.19/0.52  cnf(c_0_22, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.52  cnf(c_0_23, negated_conjecture, (k2_xboole_0(esk4_0,esk5_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.19/0.52  cnf(c_0_24, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_17])).
% 0.19/0.52  cnf(c_0_25, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.52  cnf(c_0_26, negated_conjecture, (r1_tarski(esk4_0,k2_xboole_0(esk5_0,X1))|~r1_tarski(esk3_0,k2_xboole_0(esk5_0,X1))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.52  cnf(c_0_27, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.52  cnf(c_0_28, negated_conjecture, (k2_xboole_0(esk4_0,esk3_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_22]), c_0_16])).
% 0.19/0.52  cnf(c_0_29, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_21, c_0_23])).
% 0.19/0.52  cnf(c_0_30, plain, (r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X2)|r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X1)|r1_tarski(k2_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.52  cnf(c_0_31, negated_conjecture, (r1_tarski(esk4_0,k2_xboole_0(X1,esk5_0))|~r1_tarski(esk3_0,k2_xboole_0(X1,esk5_0))), inference(spm,[status(thm)],[c_0_26, c_0_16])).
% 0.19/0.52  cnf(c_0_32, negated_conjecture, (r1_tarski(X1,esk4_0)|~r2_hidden(esk1_2(X1,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.52  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_2(k2_xboole_0(esk5_0,X1),X2),esk4_0)|r2_hidden(esk1_2(k2_xboole_0(esk5_0,X1),X2),X1)|r1_tarski(k2_xboole_0(esk5_0,X1),X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.52  cnf(c_0_34, negated_conjecture, (r1_tarski(esk4_0,k2_xboole_0(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_31, c_0_19])).
% 0.19/0.52  cnf(c_0_35, negated_conjecture, (r1_tarski(k2_xboole_0(esk3_0,esk5_0),esk4_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_16]), c_0_16]), c_0_20])).
% 0.19/0.52  cnf(c_0_36, negated_conjecture, (k2_xboole_0(esk4_0,k2_xboole_0(esk3_0,esk5_0))=k2_xboole_0(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_14, c_0_34])).
% 0.19/0.52  cnf(c_0_37, negated_conjecture, (esk4_0!=k2_xboole_0(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.52  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_35]), c_0_16]), c_0_36]), c_0_37]), ['proof']).
% 0.19/0.52  # SZS output end CNFRefutation
% 0.19/0.52  # Proof object total steps             : 39
% 0.19/0.52  # Proof object clause steps            : 26
% 0.19/0.52  # Proof object formula steps           : 13
% 0.19/0.52  # Proof object conjectures             : 18
% 0.19/0.52  # Proof object clause conjectures      : 15
% 0.19/0.52  # Proof object formula conjectures     : 3
% 0.19/0.52  # Proof object initial clauses used    : 11
% 0.19/0.52  # Proof object initial formulas used   : 6
% 0.19/0.52  # Proof object generating inferences   : 13
% 0.19/0.52  # Proof object simplifying inferences  : 10
% 0.19/0.52  # Training examples: 0 positive, 0 negative
% 0.19/0.52  # Parsed axioms                        : 6
% 0.19/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.52  # Initial clauses                      : 16
% 0.19/0.52  # Removed in clause preprocessing      : 0
% 0.19/0.52  # Initial clauses in saturation        : 16
% 0.19/0.52  # Processed clauses                    : 1970
% 0.19/0.52  # ...of these trivial                  : 455
% 0.19/0.52  # ...subsumed                          : 1050
% 0.19/0.52  # ...remaining for further processing  : 465
% 0.19/0.52  # Other redundant clauses eliminated   : 3
% 0.19/0.52  # Clauses deleted for lack of memory   : 0
% 0.19/0.52  # Backward-subsumed                    : 4
% 0.19/0.52  # Backward-rewritten                   : 33
% 0.19/0.52  # Generated clauses                    : 14325
% 0.19/0.52  # ...of the previous two non-trivial   : 8938
% 0.19/0.52  # Contextual simplify-reflections      : 1
% 0.19/0.52  # Paramodulations                      : 14178
% 0.19/0.52  # Factorizations                       : 144
% 0.19/0.52  # Equation resolutions                 : 3
% 0.19/0.52  # Propositional unsat checks           : 0
% 0.19/0.52  #    Propositional check models        : 0
% 0.19/0.52  #    Propositional check unsatisfiable : 0
% 0.19/0.52  #    Propositional clauses             : 0
% 0.19/0.52  #    Propositional clauses after purity: 0
% 0.19/0.52  #    Propositional unsat core size     : 0
% 0.19/0.52  #    Propositional preprocessing time  : 0.000
% 0.19/0.52  #    Propositional encoding time       : 0.000
% 0.19/0.52  #    Propositional solver time         : 0.000
% 0.19/0.52  #    Success case prop preproc time    : 0.000
% 0.19/0.52  #    Success case prop encoding time   : 0.000
% 0.19/0.52  #    Success case prop solver time     : 0.000
% 0.19/0.52  # Current number of processed clauses  : 409
% 0.19/0.52  #    Positive orientable unit clauses  : 201
% 0.19/0.52  #    Positive unorientable unit clauses: 1
% 0.19/0.52  #    Negative unit clauses             : 2
% 0.19/0.52  #    Non-unit-clauses                  : 205
% 0.19/0.52  # Current number of unprocessed clauses: 6929
% 0.19/0.52  # ...number of literals in the above   : 19835
% 0.19/0.52  # Current number of archived formulas  : 0
% 0.19/0.52  # Current number of archived clauses   : 53
% 0.19/0.52  # Clause-clause subsumption calls (NU) : 9593
% 0.19/0.52  # Rec. Clause-clause subsumption calls : 8944
% 0.19/0.52  # Non-unit clause-clause subsumptions  : 1046
% 0.19/0.52  # Unit Clause-clause subsumption calls : 103
% 0.19/0.52  # Rewrite failures with RHS unbound    : 0
% 0.19/0.52  # BW rewrite match attempts            : 2295
% 0.19/0.52  # BW rewrite match successes           : 43
% 0.19/0.52  # Condensation attempts                : 0
% 0.19/0.52  # Condensation successes               : 0
% 0.19/0.52  # Termbank termtop insertions          : 190944
% 0.19/0.52  
% 0.19/0.52  # -------------------------------------------------
% 0.19/0.52  # User time                : 0.167 s
% 0.19/0.52  # System time              : 0.012 s
% 0.19/0.52  # Total time               : 0.179 s
% 0.19/0.52  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
