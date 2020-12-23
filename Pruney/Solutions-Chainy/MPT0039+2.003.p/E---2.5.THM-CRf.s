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
% DateTime   : Thu Dec  3 10:32:01 EST 2020

% Result     : Theorem 16.05s
% Output     : CNFRefutation 16.05s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 131 expanded)
%              Number of clauses        :   32 (  63 expanded)
%              Number of leaves         :    3 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  110 ( 655 expanded)
%              Number of equality atoms :   30 ( 186 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t32_xboole_1])).

fof(c_0_4,plain,(
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

fof(c_0_5,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k4_xboole_0(esk4_0,esk3_0)
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k4_xboole_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

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

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | X2 != k4_xboole_0(esk3_0,esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),esk3_0)
    | r1_tarski(esk4_0,X1)
    | X2 != k4_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),esk3_0)
    | r1_tarski(esk4_0,X1) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_7])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,X3))
    | r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_11])).

cnf(c_0_19,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),esk4_0)
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( X1 = k4_xboole_0(esk4_0,X2)
    | r2_hidden(esk2_3(esk4_0,X2,X1),esk3_0)
    | r2_hidden(esk2_3(esk4_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( k4_xboole_0(esk4_0,X1) = esk3_0
    | r2_hidden(esk2_3(esk4_0,X1,esk3_0),esk3_0) ),
    inference(ef,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( X1 != k4_xboole_0(esk3_0,esk4_0)
    | ~ r2_hidden(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_7]),c_0_26])).

cnf(c_0_30,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( k4_xboole_0(esk4_0,X1) = esk3_0
    | r2_hidden(esk2_3(esk4_0,X1,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( k4_xboole_0(esk4_0,X1) = esk3_0
    | r2_hidden(esk2_3(esk4_0,X1,esk3_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_28]),c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(esk3_0,esk4_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_35]),c_0_36]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:01:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 16.05/16.26  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 16.05/16.26  # and selection function SelectNewComplexAHP.
% 16.05/16.26  #
% 16.05/16.26  # Preprocessing time       : 0.026 s
% 16.05/16.26  
% 16.05/16.26  # Proof found!
% 16.05/16.26  # SZS status Theorem
% 16.05/16.26  # SZS output start CNFRefutation
% 16.05/16.26  fof(t32_xboole_1, conjecture, ![X1, X2]:(k4_xboole_0(X1,X2)=k4_xboole_0(X2,X1)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_xboole_1)).
% 16.05/16.26  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 16.05/16.26  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 16.05/16.26  fof(c_0_3, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(X1,X2)=k4_xboole_0(X2,X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t32_xboole_1])).
% 16.05/16.26  fof(c_0_4, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 16.05/16.26  fof(c_0_5, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k4_xboole_0(esk4_0,esk3_0)&esk3_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 16.05/16.26  cnf(c_0_6, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 16.05/16.26  cnf(c_0_7, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k4_xboole_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 16.05/16.26  cnf(c_0_8, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 16.05/16.26  fof(c_0_9, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 16.05/16.26  cnf(c_0_10, negated_conjecture, (r2_hidden(X1,esk3_0)|X2!=k4_xboole_0(esk3_0,esk4_0)|~r2_hidden(X1,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_7]), c_0_8])).
% 16.05/16.26  cnf(c_0_11, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 16.05/16.26  cnf(c_0_12, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),esk3_0)|r1_tarski(esk4_0,X1)|X2!=k4_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 16.05/16.26  cnf(c_0_13, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_8])).
% 16.05/16.26  cnf(c_0_14, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_6])).
% 16.05/16.26  cnf(c_0_15, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 16.05/16.26  cnf(c_0_16, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),esk3_0)|r1_tarski(esk4_0,X1)), inference(er,[status(thm)],[c_0_12])).
% 16.05/16.26  cnf(c_0_17, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,k4_xboole_0(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_13, c_0_7])).
% 16.05/16.26  cnf(c_0_18, plain, (r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,X3))|r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_14, c_0_11])).
% 16.05/16.26  cnf(c_0_19, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 16.05/16.26  cnf(c_0_20, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 16.05/16.26  cnf(c_0_21, negated_conjecture, (r2_hidden(esk1_2(esk3_0,X1),esk4_0)|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 16.05/16.26  cnf(c_0_22, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 16.05/16.26  cnf(c_0_23, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 16.05/16.26  cnf(c_0_24, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_15, c_0_21])).
% 16.05/16.26  cnf(c_0_25, negated_conjecture, (X1=k4_xboole_0(esk4_0,X2)|r2_hidden(esk2_3(esk4_0,X2,X1),esk3_0)|r2_hidden(esk2_3(esk4_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 16.05/16.26  cnf(c_0_26, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 16.05/16.26  cnf(c_0_27, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_24])).
% 16.05/16.26  cnf(c_0_28, negated_conjecture, (k4_xboole_0(esk4_0,X1)=esk3_0|r2_hidden(esk2_3(esk4_0,X1,esk3_0),esk3_0)), inference(ef,[status(thm)],[c_0_25])).
% 16.05/16.26  cnf(c_0_29, negated_conjecture, (X1!=k4_xboole_0(esk3_0,esk4_0)|~r2_hidden(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_7]), c_0_26])).
% 16.05/16.26  cnf(c_0_30, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 16.05/16.26  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_23])).
% 16.05/16.26  cnf(c_0_32, negated_conjecture, (k4_xboole_0(esk4_0,X1)=esk3_0|r2_hidden(esk2_3(esk4_0,X1,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 16.05/16.26  cnf(c_0_33, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk3_0,esk4_0))), inference(er,[status(thm)],[c_0_29])).
% 16.05/16.26  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_31])).
% 16.05/16.26  cnf(c_0_35, negated_conjecture, (k4_xboole_0(esk4_0,X1)=esk3_0|r2_hidden(esk2_3(esk4_0,X1,esk3_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_28]), c_0_32])).
% 16.05/16.26  cnf(c_0_36, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(esk3_0,esk4_0))=X1), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 16.05/16.26  cnf(c_0_37, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 16.05/16.26  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_35]), c_0_36]), c_0_37]), ['proof']).
% 16.05/16.26  # SZS output end CNFRefutation
% 16.05/16.26  # Proof object total steps             : 39
% 16.05/16.26  # Proof object clause steps            : 32
% 16.05/16.26  # Proof object formula steps           : 7
% 16.05/16.26  # Proof object conjectures             : 22
% 16.05/16.26  # Proof object clause conjectures      : 19
% 16.05/16.26  # Proof object formula conjectures     : 3
% 16.05/16.26  # Proof object initial clauses used    : 10
% 16.05/16.26  # Proof object initial formulas used   : 3
% 16.05/16.26  # Proof object generating inferences   : 22
% 16.05/16.26  # Proof object simplifying inferences  : 6
% 16.05/16.26  # Training examples: 0 positive, 0 negative
% 16.05/16.26  # Parsed axioms                        : 3
% 16.05/16.26  # Removed by relevancy pruning/SinE    : 0
% 16.05/16.26  # Initial clauses                      : 11
% 16.05/16.26  # Removed in clause preprocessing      : 0
% 16.05/16.26  # Initial clauses in saturation        : 11
% 16.05/16.26  # Processed clauses                    : 227630
% 16.05/16.26  # ...of these trivial                  : 1457
% 16.05/16.26  # ...subsumed                          : 221292
% 16.05/16.26  # ...remaining for further processing  : 4881
% 16.05/16.26  # Other redundant clauses eliminated   : 1017
% 16.05/16.26  # Clauses deleted for lack of memory   : 0
% 16.05/16.26  # Backward-subsumed                    : 296
% 16.05/16.26  # Backward-rewritten                   : 30
% 16.05/16.26  # Generated clauses                    : 2444262
% 16.05/16.26  # ...of the previous two non-trivial   : 2192987
% 16.05/16.26  # Contextual simplify-reflections      : 119
% 16.05/16.26  # Paramodulations                      : 2440654
% 16.05/16.26  # Factorizations                       : 222
% 16.05/16.26  # Equation resolutions                 : 1919
% 16.05/16.26  # Propositional unsat checks           : 0
% 16.05/16.26  #    Propositional check models        : 0
% 16.05/16.26  #    Propositional check unsatisfiable : 0
% 16.05/16.26  #    Propositional clauses             : 0
% 16.05/16.26  #    Propositional clauses after purity: 0
% 16.05/16.26  #    Propositional unsat core size     : 0
% 16.05/16.26  #    Propositional preprocessing time  : 0.000
% 16.05/16.26  #    Propositional encoding time       : 0.000
% 16.05/16.26  #    Propositional solver time         : 0.000
% 16.05/16.26  #    Success case prop preproc time    : 0.000
% 16.05/16.26  #    Success case prop encoding time   : 0.000
% 16.05/16.26  #    Success case prop solver time     : 0.000
% 16.05/16.26  # Current number of processed clauses  : 4555
% 16.05/16.26  #    Positive orientable unit clauses  : 368
% 16.05/16.26  #    Positive unorientable unit clauses: 2
% 16.05/16.26  #    Negative unit clauses             : 96
% 16.05/16.26  #    Non-unit-clauses                  : 4089
% 16.05/16.26  # Current number of unprocessed clauses: 1959460
% 16.05/16.26  # ...number of literals in the above   : 5618667
% 16.05/16.26  # Current number of archived formulas  : 0
% 16.05/16.26  # Current number of archived clauses   : 326
% 16.05/16.26  # Clause-clause subsumption calls (NU) : 4707770
% 16.05/16.26  # Rec. Clause-clause subsumption calls : 3200621
% 16.05/16.26  # Non-unit clause-clause subsumptions  : 128414
% 16.05/16.26  # Unit Clause-clause subsumption calls : 68751
% 16.05/16.26  # Rewrite failures with RHS unbound    : 47
% 16.05/16.26  # BW rewrite match attempts            : 6920
% 16.05/16.26  # BW rewrite match successes           : 23
% 16.05/16.26  # Condensation attempts                : 0
% 16.05/16.26  # Condensation successes               : 0
% 16.05/16.26  # Termbank termtop insertions          : 46256493
% 16.14/16.32  
% 16.14/16.32  # -------------------------------------------------
% 16.14/16.32  # User time                : 15.269 s
% 16.14/16.32  # System time              : 0.707 s
% 16.14/16.32  # Total time               : 15.976 s
% 16.14/16.32  # Maximum resident set size: 1552 pages
%------------------------------------------------------------------------------
