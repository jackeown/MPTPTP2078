%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:52 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 180 expanded)
%              Number of clauses        :   38 (  90 expanded)
%              Number of leaves         :    5 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  136 ( 911 expanded)
%              Number of equality atoms :   28 ( 226 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t20_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & ! [X4] :
            ( ( r1_tarski(X4,X2)
              & r1_tarski(X4,X3) )
           => r1_tarski(X4,X1) ) )
     => X1 = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_5,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | ~ r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X1,X3)
          & ! [X4] :
              ( ( r1_tarski(X4,X2)
                & r1_tarski(X4,X3) )
             => r1_tarski(X4,X1) ) )
       => X1 = k3_xboole_0(X2,X3) ) ),
    inference(assume_negation,[status(cth)],[t20_xboole_1])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,negated_conjecture,(
    ! [X27] :
      ( r1_tarski(esk3_0,esk4_0)
      & r1_tarski(esk3_0,esk5_0)
      & ( ~ r1_tarski(X27,esk4_0)
        | ~ r1_tarski(X27,esk5_0)
        | r1_tarski(X27,esk3_0) )
      & esk3_0 != k3_xboole_0(esk4_0,esk5_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

fof(c_0_12,plain,(
    ! [X22,X23] : r1_tarski(k3_xboole_0(X22,X23),X22) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X3)
    | ~ r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),esk5_0)
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk5_0,X1),esk3_0)
    | ~ r1_tarski(k3_xboole_0(esk5_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk3_0,k3_xboole_0(X1,esk5_0))
    | ~ r2_hidden(esk1_2(esk3_0,k3_xboole_0(X1,esk5_0)),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),esk4_0)
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_23])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk2_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_25])).

cnf(c_0_31,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | r2_hidden(esk2_3(X2,X3,X1),X1)
    | r2_hidden(esk2_3(X2,X3,X1),X4)
    | ~ r1_tarski(X3,X4) ),
    inference(spm,[status(thm)],[c_0_9,c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk5_0),esk3_0)
    | ~ r1_tarski(k3_xboole_0(X1,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_9,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk3_0,k3_xboole_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_30,c_0_25])).

cnf(c_0_36,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | r2_hidden(esk2_3(X2,X3,X1),X1)
    | ~ r1_tarski(X3,X1) ),
    inference(ef,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_19])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_39,negated_conjecture,
    ( k3_xboole_0(X1,esk3_0) = esk3_0
    | r2_hidden(esk2_3(X1,esk3_0,esk3_0),k3_xboole_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( X1 = X2
    | ~ r2_hidden(esk2_3(X2,X2,X1),X1)
    | ~ r2_hidden(esk2_3(X2,X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k3_xboole_0(X1,k3_xboole_0(esk4_0,esk5_0)) = esk3_0
    | r2_hidden(esk2_3(X1,k3_xboole_0(esk4_0,esk5_0),esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( esk3_0 != k3_xboole_0(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_xboole_0(esk4_0,esk5_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_39]),c_0_27])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_hidden(esk2_3(k3_xboole_0(esk4_0,esk5_0),k3_xboole_0(esk4_0,esk5_0),esk3_0),k3_xboole_0(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_35])]),c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(X1,k3_xboole_0(esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(esk2_3(k3_xboole_0(esk4_0,esk5_0),k3_xboole_0(esk4_0,esk5_0),esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_41]),c_0_35]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.49  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.19/0.49  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.49  #
% 0.19/0.49  # Preprocessing time       : 0.027 s
% 0.19/0.49  # Presaturation interreduction done
% 0.19/0.49  
% 0.19/0.49  # Proof found!
% 0.19/0.49  # SZS status Theorem
% 0.19/0.49  # SZS output start CNFRefutation
% 0.19/0.49  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.19/0.49  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.49  fof(t20_xboole_1, conjecture, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&![X4]:((r1_tarski(X4,X2)&r1_tarski(X4,X3))=>r1_tarski(X4,X1)))=>X1=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 0.19/0.49  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.19/0.49  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.49  fof(c_0_5, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k3_xboole_0(X13,X14))&(r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k3_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|~r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k3_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|~r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k3_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k3_xboole_0(X18,X19))&(r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k3_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.19/0.49  fof(c_0_6, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.49  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&![X4]:((r1_tarski(X4,X2)&r1_tarski(X4,X3))=>r1_tarski(X4,X1)))=>X1=k3_xboole_0(X2,X3))), inference(assume_negation,[status(cth)],[t20_xboole_1])).
% 0.19/0.49  cnf(c_0_8, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.49  cnf(c_0_9, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.49  cnf(c_0_10, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.49  fof(c_0_11, negated_conjecture, ![X27]:(((r1_tarski(esk3_0,esk4_0)&r1_tarski(esk3_0,esk5_0))&(~r1_tarski(X27,esk4_0)|~r1_tarski(X27,esk5_0)|r1_tarski(X27,esk3_0)))&esk3_0!=k3_xboole_0(esk4_0,esk5_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.19/0.49  fof(c_0_12, plain, ![X22, X23]:r1_tarski(k3_xboole_0(X22,X23),X22), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.19/0.49  cnf(c_0_13, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.49  cnf(c_0_14, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_8])).
% 0.19/0.49  cnf(c_0_15, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.19/0.49  cnf(c_0_16, negated_conjecture, (r1_tarski(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.49  cnf(c_0_17, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.49  cnf(c_0_18, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,esk4_0)|~r1_tarski(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.49  cnf(c_0_19, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.49  fof(c_0_20, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.49  cnf(c_0_21, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X3)|~r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.49  cnf(c_0_22, negated_conjecture, (r2_hidden(esk1_2(esk3_0,X1),esk5_0)|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.49  cnf(c_0_23, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.49  cnf(c_0_24, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.49  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk2_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_17])).
% 0.19/0.49  cnf(c_0_26, negated_conjecture, (r1_tarski(k3_xboole_0(esk5_0,X1),esk3_0)|~r1_tarski(k3_xboole_0(esk5_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.49  cnf(c_0_27, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.49  cnf(c_0_28, negated_conjecture, (r1_tarski(esk3_0,k3_xboole_0(X1,esk5_0))|~r2_hidden(esk1_2(esk3_0,k3_xboole_0(X1,esk5_0)),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.49  cnf(c_0_29, negated_conjecture, (r2_hidden(esk1_2(esk3_0,X1),esk4_0)|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_15, c_0_23])).
% 0.19/0.49  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=X2|~r2_hidden(esk2_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_25])).
% 0.19/0.49  cnf(c_0_31, plain, (X1=k3_xboole_0(X2,X3)|r2_hidden(esk2_3(X2,X3,X1),X1)|r2_hidden(esk2_3(X2,X3,X1),X4)|~r1_tarski(X3,X4)), inference(spm,[status(thm)],[c_0_9, c_0_17])).
% 0.19/0.49  cnf(c_0_32, negated_conjecture, (r1_tarski(k3_xboole_0(X1,esk5_0),esk3_0)|~r1_tarski(k3_xboole_0(X1,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.49  cnf(c_0_33, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk2_3(X1,X2,X2),X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_9, c_0_25])).
% 0.19/0.49  cnf(c_0_34, negated_conjecture, (r1_tarski(esk3_0,k3_xboole_0(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.49  cnf(c_0_35, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_30, c_0_25])).
% 0.19/0.49  cnf(c_0_36, plain, (X1=k3_xboole_0(X2,X3)|r2_hidden(esk2_3(X2,X3,X1),X1)|~r1_tarski(X3,X1)), inference(ef,[status(thm)],[c_0_31])).
% 0.19/0.49  cnf(c_0_37, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_32, c_0_19])).
% 0.19/0.49  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.49  cnf(c_0_39, negated_conjecture, (k3_xboole_0(X1,esk3_0)=esk3_0|r2_hidden(esk2_3(X1,esk3_0,esk3_0),k3_xboole_0(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.49  cnf(c_0_40, plain, (X1=X2|~r2_hidden(esk2_3(X2,X2,X1),X1)|~r2_hidden(esk2_3(X2,X2,X1),X2)), inference(spm,[status(thm)],[c_0_24, c_0_35])).
% 0.19/0.49  cnf(c_0_41, negated_conjecture, (k3_xboole_0(X1,k3_xboole_0(esk4_0,esk5_0))=esk3_0|r2_hidden(esk2_3(X1,k3_xboole_0(esk4_0,esk5_0),esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.49  cnf(c_0_42, negated_conjecture, (esk3_0!=k3_xboole_0(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.49  cnf(c_0_43, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_38])).
% 0.19/0.49  cnf(c_0_44, negated_conjecture, (k3_xboole_0(esk3_0,k3_xboole_0(esk4_0,esk5_0))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_39]), c_0_27])).
% 0.19/0.49  cnf(c_0_45, negated_conjecture, (~r2_hidden(esk2_3(k3_xboole_0(esk4_0,esk5_0),k3_xboole_0(esk4_0,esk5_0),esk3_0),k3_xboole_0(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_35])]), c_0_42])).
% 0.19/0.49  cnf(c_0_46, negated_conjecture, (r2_hidden(X1,k3_xboole_0(esk4_0,esk5_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.49  cnf(c_0_47, negated_conjecture, (~r2_hidden(esk2_3(k3_xboole_0(esk4_0,esk5_0),k3_xboole_0(esk4_0,esk5_0),esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.49  cnf(c_0_48, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_41]), c_0_35]), c_0_42]), ['proof']).
% 0.19/0.49  # SZS output end CNFRefutation
% 0.19/0.49  # Proof object total steps             : 49
% 0.19/0.49  # Proof object clause steps            : 38
% 0.19/0.49  # Proof object formula steps           : 11
% 0.19/0.49  # Proof object conjectures             : 21
% 0.19/0.49  # Proof object clause conjectures      : 18
% 0.19/0.49  # Proof object formula conjectures     : 3
% 0.19/0.49  # Proof object initial clauses used    : 13
% 0.19/0.49  # Proof object initial formulas used   : 5
% 0.19/0.49  # Proof object generating inferences   : 23
% 0.19/0.49  # Proof object simplifying inferences  : 9
% 0.19/0.49  # Training examples: 0 positive, 0 negative
% 0.19/0.49  # Parsed axioms                        : 5
% 0.19/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.49  # Initial clauses                      : 15
% 0.19/0.49  # Removed in clause preprocessing      : 0
% 0.19/0.49  # Initial clauses in saturation        : 15
% 0.19/0.49  # Processed clauses                    : 1186
% 0.19/0.49  # ...of these trivial                  : 224
% 0.19/0.49  # ...subsumed                          : 605
% 0.19/0.49  # ...remaining for further processing  : 357
% 0.19/0.49  # Other redundant clauses eliminated   : 3
% 0.19/0.49  # Clauses deleted for lack of memory   : 0
% 0.19/0.49  # Backward-subsumed                    : 0
% 0.19/0.49  # Backward-rewritten                   : 50
% 0.19/0.49  # Generated clauses                    : 8045
% 0.19/0.49  # ...of the previous two non-trivial   : 6013
% 0.19/0.49  # Contextual simplify-reflections      : 10
% 0.19/0.49  # Paramodulations                      : 7968
% 0.19/0.49  # Factorizations                       : 74
% 0.19/0.49  # Equation resolutions                 : 3
% 0.19/0.49  # Propositional unsat checks           : 0
% 0.19/0.49  #    Propositional check models        : 0
% 0.19/0.49  #    Propositional check unsatisfiable : 0
% 0.19/0.49  #    Propositional clauses             : 0
% 0.19/0.49  #    Propositional clauses after purity: 0
% 0.19/0.49  #    Propositional unsat core size     : 0
% 0.19/0.49  #    Propositional preprocessing time  : 0.000
% 0.19/0.49  #    Propositional encoding time       : 0.000
% 0.19/0.49  #    Propositional solver time         : 0.000
% 0.19/0.49  #    Success case prop preproc time    : 0.000
% 0.19/0.49  #    Success case prop encoding time   : 0.000
% 0.19/0.49  #    Success case prop solver time     : 0.000
% 0.19/0.49  # Current number of processed clauses  : 289
% 0.19/0.49  #    Positive orientable unit clauses  : 102
% 0.19/0.49  #    Positive unorientable unit clauses: 1
% 0.19/0.49  #    Negative unit clauses             : 3
% 0.19/0.49  #    Non-unit-clauses                  : 183
% 0.19/0.49  # Current number of unprocessed clauses: 4816
% 0.19/0.49  # ...number of literals in the above   : 14606
% 0.19/0.49  # Current number of archived formulas  : 0
% 0.19/0.49  # Current number of archived clauses   : 65
% 0.19/0.49  # Clause-clause subsumption calls (NU) : 5679
% 0.19/0.49  # Rec. Clause-clause subsumption calls : 4576
% 0.19/0.49  # Non-unit clause-clause subsumptions  : 615
% 0.19/0.49  # Unit Clause-clause subsumption calls : 609
% 0.19/0.49  # Rewrite failures with RHS unbound    : 0
% 0.19/0.49  # BW rewrite match attempts            : 382
% 0.19/0.49  # BW rewrite match successes           : 34
% 0.19/0.49  # Condensation attempts                : 0
% 0.19/0.49  # Condensation successes               : 0
% 0.19/0.49  # Termbank termtop insertions          : 119102
% 0.19/0.49  
% 0.19/0.49  # -------------------------------------------------
% 0.19/0.49  # User time                : 0.135 s
% 0.19/0.49  # System time              : 0.013 s
% 0.19/0.49  # Total time               : 0.148 s
% 0.19/0.49  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
