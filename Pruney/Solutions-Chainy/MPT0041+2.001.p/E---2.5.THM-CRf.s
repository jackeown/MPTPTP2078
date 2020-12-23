%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:01 EST 2020

% Result     : Theorem 1.27s
% Output     : CNFRefutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   35 (  86 expanded)
%              Number of clauses        :   28 (  46 expanded)
%              Number of leaves         :    3 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  100 ( 469 expanded)
%              Number of equality atoms :   18 ( 117 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t34_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_3,plain,(
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

cnf(c_0_4,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,X2)
       => r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1)) ) ),
    inference(assume_negation,[status(cth)],[t34_xboole_1])).

cnf(c_0_6,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_4])).

fof(c_0_9,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_10,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k4_xboole_0(esk5_0,esk4_0),k4_xboole_0(esk5_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = X1
    | ~ r2_hidden(esk2_3(X1,k4_xboole_0(X2,X3),X1),X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_16])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_17,c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( k4_xboole_0(esk3_0,X1) = esk3_0
    | r2_hidden(esk2_3(esk3_0,X1,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_8])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X1)
    | r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_16])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),k4_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,esk4_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_23])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),k4_xboole_0(X1,X4))
    | r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X4)
    | r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk4_0),X2)
    | ~ r2_hidden(esk1_2(k4_xboole_0(X1,esk4_0),X2),esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)),X3)
    | r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk5_0,esk4_0),k4_xboole_0(esk5_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk4_0),k4_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.27/1.43  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 1.27/1.43  # and selection function SelectNewComplexAHP.
% 1.27/1.43  #
% 1.27/1.43  # Preprocessing time       : 0.027 s
% 1.27/1.43  
% 1.27/1.43  # Proof found!
% 1.27/1.43  # SZS status Theorem
% 1.27/1.43  # SZS output start CNFRefutation
% 1.27/1.43  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.27/1.43  fof(t34_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 1.27/1.43  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.27/1.43  fof(c_0_3, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 1.27/1.43  cnf(c_0_4, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 1.27/1.43  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1)))), inference(assume_negation,[status(cth)],[t34_xboole_1])).
% 1.27/1.43  cnf(c_0_6, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 1.27/1.43  cnf(c_0_7, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 1.27/1.43  cnf(c_0_8, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_4])).
% 1.27/1.43  fof(c_0_9, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.27/1.43  fof(c_0_10, negated_conjecture, (r1_tarski(esk3_0,esk4_0)&~r1_tarski(k4_xboole_0(esk5_0,esk4_0),k4_xboole_0(esk5_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 1.27/1.43  cnf(c_0_11, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_6])).
% 1.27/1.43  cnf(c_0_12, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_8])).
% 1.27/1.43  cnf(c_0_13, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.27/1.43  cnf(c_0_14, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.27/1.43  cnf(c_0_15, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 1.27/1.43  cnf(c_0_16, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.27/1.43  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=X1|~r2_hidden(esk2_3(X1,k4_xboole_0(X2,X3),X1),X3)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 1.27/1.43  cnf(c_0_18, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 1.27/1.43  cnf(c_0_19, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 1.27/1.43  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_15])).
% 1.27/1.43  cnf(c_0_21, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X2)), inference(spm,[status(thm)],[c_0_11, c_0_16])).
% 1.27/1.43  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_17, c_0_8])).
% 1.27/1.43  cnf(c_0_23, negated_conjecture, (k4_xboole_0(esk3_0,X1)=esk3_0|r2_hidden(esk2_3(esk3_0,X1,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_8])).
% 1.27/1.43  cnf(c_0_24, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_19])).
% 1.27/1.43  cnf(c_0_25, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X1)|r1_tarski(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_20, c_0_16])).
% 1.27/1.43  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),k4_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 1.27/1.43  cnf(c_0_27, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,esk4_0))=esk3_0), inference(spm,[status(thm)],[c_0_17, c_0_23])).
% 1.27/1.43  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.27/1.43  cnf(c_0_29, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),k4_xboole_0(X1,X4))|r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X4)|r1_tarski(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 1.27/1.43  cnf(c_0_30, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk4_0),X2)|~r2_hidden(esk1_2(k4_xboole_0(X1,esk4_0),X2),esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 1.27/1.43  cnf(c_0_31, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)),X3)|r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 1.27/1.43  cnf(c_0_32, negated_conjecture, (~r1_tarski(k4_xboole_0(esk5_0,esk4_0),k4_xboole_0(esk5_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.27/1.43  cnf(c_0_33, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk4_0),k4_xboole_0(X1,esk3_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 1.27/1.43  cnf(c_0_34, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33])]), ['proof']).
% 1.27/1.43  # SZS output end CNFRefutation
% 1.27/1.43  # Proof object total steps             : 35
% 1.27/1.43  # Proof object clause steps            : 28
% 1.27/1.43  # Proof object formula steps           : 7
% 1.27/1.43  # Proof object conjectures             : 11
% 1.27/1.43  # Proof object clause conjectures      : 8
% 1.27/1.43  # Proof object formula conjectures     : 3
% 1.27/1.43  # Proof object initial clauses used    : 10
% 1.27/1.43  # Proof object initial formulas used   : 3
% 1.27/1.43  # Proof object generating inferences   : 17
% 1.27/1.43  # Proof object simplifying inferences  : 3
% 1.27/1.43  # Training examples: 0 positive, 0 negative
% 1.27/1.43  # Parsed axioms                        : 3
% 1.27/1.43  # Removed by relevancy pruning/SinE    : 0
% 1.27/1.43  # Initial clauses                      : 11
% 1.27/1.43  # Removed in clause preprocessing      : 0
% 1.27/1.43  # Initial clauses in saturation        : 11
% 1.27/1.43  # Processed clauses                    : 21991
% 1.27/1.43  # ...of these trivial                  : 416
% 1.27/1.43  # ...subsumed                          : 20662
% 1.27/1.43  # ...remaining for further processing  : 913
% 1.27/1.43  # Other redundant clauses eliminated   : 244
% 1.27/1.43  # Clauses deleted for lack of memory   : 0
% 1.27/1.43  # Backward-subsumed                    : 46
% 1.27/1.43  # Backward-rewritten                   : 7
% 1.27/1.43  # Generated clauses                    : 158606
% 1.27/1.43  # ...of the previous two non-trivial   : 127025
% 1.27/1.43  # Contextual simplify-reflections      : 8
% 1.27/1.43  # Paramodulations                      : 158172
% 1.27/1.43  # Factorizations                       : 96
% 1.27/1.43  # Equation resolutions                 : 338
% 1.27/1.43  # Propositional unsat checks           : 0
% 1.27/1.43  #    Propositional check models        : 0
% 1.27/1.43  #    Propositional check unsatisfiable : 0
% 1.27/1.43  #    Propositional clauses             : 0
% 1.27/1.43  #    Propositional clauses after purity: 0
% 1.27/1.43  #    Propositional unsat core size     : 0
% 1.27/1.43  #    Propositional preprocessing time  : 0.000
% 1.27/1.43  #    Propositional encoding time       : 0.000
% 1.27/1.43  #    Propositional solver time         : 0.000
% 1.27/1.43  #    Success case prop preproc time    : 0.000
% 1.27/1.43  #    Success case prop encoding time   : 0.000
% 1.27/1.43  #    Success case prop solver time     : 0.000
% 1.27/1.43  # Current number of processed clauses  : 860
% 1.27/1.43  #    Positive orientable unit clauses  : 127
% 1.27/1.43  #    Positive unorientable unit clauses: 2
% 1.27/1.43  #    Negative unit clauses             : 8
% 1.27/1.43  #    Non-unit-clauses                  : 723
% 1.27/1.43  # Current number of unprocessed clauses: 105013
% 1.27/1.43  # ...number of literals in the above   : 280014
% 1.27/1.43  # Current number of archived formulas  : 0
% 1.27/1.43  # Current number of archived clauses   : 53
% 1.27/1.43  # Clause-clause subsumption calls (NU) : 196729
% 1.27/1.43  # Rec. Clause-clause subsumption calls : 140163
% 1.27/1.43  # Non-unit clause-clause subsumptions  : 14596
% 1.27/1.43  # Unit Clause-clause subsumption calls : 1279
% 1.27/1.43  # Rewrite failures with RHS unbound    : 45
% 1.27/1.43  # BW rewrite match attempts            : 976
% 1.27/1.43  # BW rewrite match successes           : 17
% 1.27/1.43  # Condensation attempts                : 0
% 1.27/1.43  # Condensation successes               : 0
% 1.27/1.43  # Termbank termtop insertions          : 2342670
% 1.27/1.44  
% 1.27/1.44  # -------------------------------------------------
% 1.27/1.44  # User time                : 1.046 s
% 1.27/1.44  # System time              : 0.051 s
% 1.27/1.44  # Total time               : 1.097 s
% 1.27/1.44  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
