%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:01 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 283 expanded)
%              Number of clauses        :   31 ( 135 expanded)
%              Number of leaves         :    7 (  71 expanded)
%              Depth                    :   16
%              Number of atoms          :  121 (1115 expanded)
%              Number of equality atoms :   30 ( 318 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t32_xboole_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t6_xboole_0,axiom,(
    ! [X1,X2] :
      ~ ( r2_xboole_0(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ~ r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(c_0_7,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_8,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t32_xboole_1])).

cnf(c_0_10,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( r2_hidden(X18,X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X18,X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X19,X15)
        | r2_hidden(X19,X16)
        | r2_hidden(X19,X17)
        | X17 != k4_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk3_3(X20,X21,X22),X22)
        | ~ r2_hidden(esk3_3(X20,X21,X22),X20)
        | r2_hidden(esk3_3(X20,X21,X22),X21)
        | X22 = k4_xboole_0(X20,X21) )
      & ( r2_hidden(esk3_3(X20,X21,X22),X20)
        | r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k4_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk3_3(X20,X21,X22),X21)
        | r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k4_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_13,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk6_0) = k4_xboole_0(esk6_0,esk5_0)
    & esk5_0 != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_14,plain,(
    ! [X24,X25] :
      ( ( r1_tarski(X24,X25)
        | ~ r2_xboole_0(X24,X25) )
      & ( X24 != X25
        | ~ r2_xboole_0(X24,X25) )
      & ( ~ r1_tarski(X24,X25)
        | X24 = X25
        | r2_xboole_0(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk6_0) = k4_xboole_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X26,X27] :
      ( ( r2_hidden(esk4_2(X26,X27),X27)
        | ~ r2_xboole_0(X26,X27) )
      & ( ~ r2_hidden(esk4_2(X26,X27),X26)
        | ~ r2_xboole_0(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).

cnf(c_0_21,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( X1 != k4_xboole_0(esk6_0,esk5_0)
    | ~ r2_hidden(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k1_xboole_0 = X1
    | r2_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk6_0,esk5_0)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk4_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( k4_xboole_0(esk6_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_23,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | X2 != k1_xboole_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_28]),c_0_30])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | r2_hidden(esk2_2(esk6_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk6_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_18,c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | X2 != k1_xboole_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_35]),c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( r2_xboole_0(esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_36]),c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk4_2(esk6_0,esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_39])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(esk4_2(X1,X2),X1)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk4_2(esk6_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.20/0.39  # and selection function SelectNewComplexAHP.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.39  fof(t32_xboole_1, conjecture, ![X1, X2]:(k4_xboole_0(X1,X2)=k4_xboole_0(X2,X1)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_xboole_1)).
% 0.20/0.39  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.39  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.20/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.39  fof(t6_xboole_0, axiom, ![X1, X2]:~((r2_xboole_0(X1,X2)&![X3]:~((r2_hidden(X3,X2)&~(r2_hidden(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 0.20/0.39  fof(c_0_7, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.39  fof(c_0_8, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.39  fof(c_0_9, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(X1,X2)=k4_xboole_0(X2,X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t32_xboole_1])).
% 0.20/0.39  cnf(c_0_10, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_11, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  fof(c_0_12, plain, ![X15, X16, X17, X18, X19, X20, X21, X22]:((((r2_hidden(X18,X15)|~r2_hidden(X18,X17)|X17!=k4_xboole_0(X15,X16))&(~r2_hidden(X18,X16)|~r2_hidden(X18,X17)|X17!=k4_xboole_0(X15,X16)))&(~r2_hidden(X19,X15)|r2_hidden(X19,X16)|r2_hidden(X19,X17)|X17!=k4_xboole_0(X15,X16)))&((~r2_hidden(esk3_3(X20,X21,X22),X22)|(~r2_hidden(esk3_3(X20,X21,X22),X20)|r2_hidden(esk3_3(X20,X21,X22),X21))|X22=k4_xboole_0(X20,X21))&((r2_hidden(esk3_3(X20,X21,X22),X20)|r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k4_xboole_0(X20,X21))&(~r2_hidden(esk3_3(X20,X21,X22),X21)|r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k4_xboole_0(X20,X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.39  fof(c_0_13, negated_conjecture, (k4_xboole_0(esk5_0,esk6_0)=k4_xboole_0(esk6_0,esk5_0)&esk5_0!=esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.20/0.39  fof(c_0_14, plain, ![X24, X25]:(((r1_tarski(X24,X25)|~r2_xboole_0(X24,X25))&(X24!=X25|~r2_xboole_0(X24,X25)))&(~r1_tarski(X24,X25)|X24=X25|r2_xboole_0(X24,X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.20/0.39  cnf(c_0_15, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.39  cnf(c_0_16, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.39  cnf(c_0_17, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_18, negated_conjecture, (k4_xboole_0(esk5_0,esk6_0)=k4_xboole_0(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_19, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  fof(c_0_20, plain, ![X26, X27]:((r2_hidden(esk4_2(X26,X27),X27)|~r2_xboole_0(X26,X27))&(~r2_hidden(esk4_2(X26,X27),X26)|~r2_xboole_0(X26,X27))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).
% 0.20/0.39  cnf(c_0_21, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_22, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.39  cnf(c_0_23, negated_conjecture, (X1!=k4_xboole_0(esk6_0,esk5_0)|~r2_hidden(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.20/0.39  cnf(c_0_24, plain, (r2_hidden(esk4_2(X1,X2),X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_25, plain, (k1_xboole_0=X1|r2_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk6_0,esk5_0))), inference(er,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_27, plain, (k1_xboole_0=X1|r2_hidden(esk4_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.39  cnf(c_0_28, negated_conjecture, (k4_xboole_0(esk6_0,esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.39  cnf(c_0_29, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_23, c_0_28])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,esk5_0)|X2!=k1_xboole_0|~r2_hidden(X1,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_28]), c_0_30])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk6_0)), inference(er,[status(thm)],[c_0_31])).
% 0.20/0.39  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  cnf(c_0_34, negated_conjecture, (r1_tarski(esk6_0,X1)|r2_hidden(esk2_2(esk6_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_11])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (k4_xboole_0(esk5_0,esk6_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_18, c_0_28])).
% 0.20/0.39  cnf(c_0_36, negated_conjecture, (r1_tarski(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, (esk5_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_38, negated_conjecture, (r2_hidden(X1,esk6_0)|X2!=k1_xboole_0|~r2_hidden(X1,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_35]), c_0_30])).
% 0.20/0.39  cnf(c_0_39, negated_conjecture, (r2_xboole_0(esk6_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_36]), c_0_37])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk5_0)), inference(er,[status(thm)],[c_0_38])).
% 0.20/0.39  cnf(c_0_41, negated_conjecture, (r2_hidden(esk4_2(esk6_0,esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_24, c_0_39])).
% 0.20/0.39  cnf(c_0_42, plain, (~r2_hidden(esk4_2(X1,X2),X1)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_43, negated_conjecture, (r2_hidden(esk4_2(esk6_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.39  cnf(c_0_44, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_39])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 45
% 0.20/0.39  # Proof object clause steps            : 31
% 0.20/0.39  # Proof object formula steps           : 14
% 0.20/0.39  # Proof object conjectures             : 20
% 0.20/0.39  # Proof object clause conjectures      : 17
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 12
% 0.20/0.39  # Proof object initial formulas used   : 7
% 0.20/0.39  # Proof object generating inferences   : 17
% 0.20/0.39  # Proof object simplifying inferences  : 8
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 7
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 19
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 19
% 0.20/0.39  # Processed clauses                    : 319
% 0.20/0.39  # ...of these trivial                  : 2
% 0.20/0.39  # ...subsumed                          : 207
% 0.20/0.39  # ...remaining for further processing  : 110
% 0.20/0.39  # Other redundant clauses eliminated   : 25
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 10
% 0.20/0.39  # Backward-rewritten                   : 6
% 0.20/0.39  # Generated clauses                    : 797
% 0.20/0.39  # ...of the previous two non-trivial   : 703
% 0.20/0.39  # Contextual simplify-reflections      : 5
% 0.20/0.39  # Paramodulations                      : 753
% 0.20/0.39  # Factorizations                       : 6
% 0.20/0.39  # Equation resolutions                 : 36
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 91
% 0.20/0.39  #    Positive orientable unit clauses  : 15
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 5
% 0.20/0.39  #    Non-unit-clauses                  : 71
% 0.20/0.39  # Current number of unprocessed clauses: 360
% 0.20/0.39  # ...number of literals in the above   : 1307
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 18
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 1325
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 852
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 192
% 0.20/0.39  # Unit Clause-clause subsumption calls : 145
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 10
% 0.20/0.39  # BW rewrite match successes           : 1
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 8416
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.043 s
% 0.20/0.39  # System time              : 0.004 s
% 0.20/0.39  # Total time               : 0.048 s
% 0.20/0.39  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
