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
% DateTime   : Thu Dec  3 10:32:01 EST 2020

% Result     : Theorem 1.18s
% Output     : CNFRefutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 553 expanded)
%              Number of clauses        :   54 ( 307 expanded)
%              Number of leaves         :    3 ( 121 expanded)
%              Depth                    :   15
%              Number of atoms          :  137 (3420 expanded)
%              Number of equality atoms :   42 (1002 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t33_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).

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

cnf(c_0_5,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,X2)
       => r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ) ),
    inference(assume_negation,[status(cth)],[t33_xboole_1])).

cnf(c_0_9,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_10,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_4])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_7])).

fof(c_0_14,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k4_xboole_0(esk3_0,esk5_0),k4_xboole_0(esk4_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_10])).

cnf(c_0_16,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X1)
    | r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = X1
    | ~ r2_hidden(esk2_3(X1,k4_xboole_0(X2,X3),X1),X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_15])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = X1
    | r2_hidden(esk2_3(X1,k4_xboole_0(X2,X3),X1),X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_15])).

cnf(c_0_22,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_20,c_0_10])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X3,X3)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_22])).

cnf(c_0_27,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_28,negated_conjecture,
    ( X1 = k4_xboole_0(esk3_0,X2)
    | r2_hidden(esk2_3(esk3_0,X2,X1),esk4_0)
    | r2_hidden(esk2_3(esk3_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_4])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r2_hidden(esk2_3(X1,X2,X1),k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_24])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,X2)
    | r2_hidden(esk2_3(k4_xboole_0(X1,X2),X3,k4_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_10])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_25]),c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( X1 = k4_xboole_0(esk3_0,esk4_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X2) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_30])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k4_xboole_0(esk3_0,X1) = esk3_0
    | r2_hidden(esk2_3(esk3_0,X1,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X4,X1)) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X3)) = X1 ),
    inference(spm,[status(thm)],[c_0_24,c_0_34])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),k4_xboole_0(X1,X3))
    | r2_hidden(esk2_3(X1,X2,X1),X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(X1,esk4_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X2,X3),X4)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_35])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4)) = X1
    | ~ r2_hidden(esk2_3(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4),X1),X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_21])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3))) = X1
    | r2_hidden(esk2_3(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3)),X1),X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_41])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),k4_xboole_0(X1,X4))
    | r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X4)
    | r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk4_0),k4_xboole_0(esk3_0,X2)) = k4_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X1,X3))) = X1 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_52,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),X2)
    | r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(esk3_0,X1),X2),esk4_0) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)),X3) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_50])).

cnf(c_0_55,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(esk4_0,X1)) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(X2,esk4_0)) = k4_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_42])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk3_0,esk5_0),k4_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,X1),k4_xboole_0(esk4_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:17:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.18/1.36  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 1.18/1.36  # and selection function SelectNewComplexAHP.
% 1.18/1.36  #
% 1.18/1.36  # Preprocessing time       : 0.026 s
% 1.18/1.36  
% 1.18/1.36  # Proof found!
% 1.18/1.36  # SZS status Theorem
% 1.18/1.36  # SZS output start CNFRefutation
% 1.18/1.36  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.18/1.36  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.18/1.36  fof(t33_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_xboole_1)).
% 1.18/1.36  fof(c_0_3, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 1.18/1.36  cnf(c_0_4, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 1.18/1.36  cnf(c_0_5, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 1.18/1.36  fof(c_0_6, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.18/1.36  cnf(c_0_7, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 1.18/1.36  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)))), inference(assume_negation,[status(cth)],[t33_xboole_1])).
% 1.18/1.36  cnf(c_0_9, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 1.18/1.36  cnf(c_0_10, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_4])).
% 1.18/1.36  cnf(c_0_11, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_5])).
% 1.18/1.36  cnf(c_0_12, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.18/1.36  cnf(c_0_13, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_7])).
% 1.18/1.36  fof(c_0_14, negated_conjecture, (r1_tarski(esk3_0,esk4_0)&~r1_tarski(k4_xboole_0(esk3_0,esk5_0),k4_xboole_0(esk4_0,esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 1.18/1.36  cnf(c_0_15, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_10])).
% 1.18/1.36  cnf(c_0_16, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X2)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 1.18/1.36  cnf(c_0_17, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X1)|r1_tarski(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_13, c_0_12])).
% 1.18/1.36  cnf(c_0_18, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.18/1.36  cnf(c_0_19, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.18/1.36  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=X1|~r2_hidden(esk2_3(X1,k4_xboole_0(X2,X3),X1),X3)), inference(spm,[status(thm)],[c_0_11, c_0_15])).
% 1.18/1.36  cnf(c_0_21, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=X1|r2_hidden(esk2_3(X1,k4_xboole_0(X2,X3),X1),X2)), inference(spm,[status(thm)],[c_0_13, c_0_15])).
% 1.18/1.36  cnf(c_0_22, plain, (r1_tarski(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 1.18/1.36  cnf(c_0_23, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 1.18/1.36  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_20, c_0_10])).
% 1.18/1.36  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 1.18/1.36  cnf(c_0_26, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X3,X3))), inference(spm,[status(thm)],[c_0_18, c_0_22])).
% 1.18/1.36  cnf(c_0_27, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 1.18/1.36  cnf(c_0_28, negated_conjecture, (X1=k4_xboole_0(esk3_0,X2)|r2_hidden(esk2_3(esk3_0,X2,X1),esk4_0)|r2_hidden(esk2_3(esk3_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_23, c_0_4])).
% 1.18/1.36  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=X1|~r2_hidden(esk2_3(X1,X2,X1),k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_20, c_0_24])).
% 1.18/1.36  cnf(c_0_30, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,X2)|r2_hidden(esk2_3(k4_xboole_0(X1,X2),X3,k4_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_13, c_0_10])).
% 1.18/1.36  cnf(c_0_31, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 1.18/1.36  cnf(c_0_32, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_25]), c_0_26])).
% 1.18/1.36  cnf(c_0_33, negated_conjecture, (X1=k4_xboole_0(esk3_0,esk4_0)|r2_hidden(esk2_3(esk3_0,esk4_0,X1),X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 1.18/1.36  cnf(c_0_34, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X2)=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 1.18/1.36  cnf(c_0_35, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_30])).
% 1.18/1.36  cnf(c_0_36, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_31])).
% 1.18/1.36  cnf(c_0_37, negated_conjecture, (k4_xboole_0(esk3_0,X1)=esk3_0|r2_hidden(esk2_3(esk3_0,X1,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_10])).
% 1.18/1.36  cnf(c_0_38, negated_conjecture, (k4_xboole_0(X1,X1)=k4_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 1.18/1.36  cnf(c_0_39, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X4,X1))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 1.18/1.36  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X3))=X1), inference(spm,[status(thm)],[c_0_24, c_0_34])).
% 1.18/1.36  cnf(c_0_41, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_3(X1,X2,X1),k4_xboole_0(X1,X3))|r2_hidden(esk2_3(X1,X2,X1),X3)), inference(spm,[status(thm)],[c_0_36, c_0_10])).
% 1.18/1.36  cnf(c_0_42, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(X1,esk4_0))=esk3_0), inference(spm,[status(thm)],[c_0_20, c_0_37])).
% 1.18/1.36  cnf(c_0_43, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k4_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 1.18/1.36  cnf(c_0_44, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X2,X3),X4))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_35])).
% 1.18/1.36  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4))=X1|~r2_hidden(esk2_3(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4),X1),X3)), inference(spm,[status(thm)],[c_0_11, c_0_21])).
% 1.18/1.36  cnf(c_0_46, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3)))=X1|r2_hidden(esk2_3(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3)),X1),X3)), inference(spm,[status(thm)],[c_0_20, c_0_41])).
% 1.18/1.36  cnf(c_0_47, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),k4_xboole_0(X1,X4))|r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X4)|r1_tarski(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_36, c_0_17])).
% 1.18/1.36  cnf(c_0_48, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk4_0),k4_xboole_0(esk3_0,X2))=k4_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_42])).
% 1.18/1.36  cnf(c_0_49, negated_conjecture, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1)=k4_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 1.18/1.36  cnf(c_0_50, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X1,X3)))=X1), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 1.18/1.36  cnf(c_0_51, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.18/1.36  cnf(c_0_52, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),X2)|r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_16, c_0_47])).
% 1.18/1.36  cnf(c_0_53, negated_conjecture, (k4_xboole_0(k4_xboole_0(k4_xboole_0(esk3_0,X1),X2),esk4_0)=k4_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 1.18/1.36  cnf(c_0_54, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)),X3)=k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_24, c_0_50])).
% 1.18/1.36  cnf(c_0_55, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 1.18/1.36  cnf(c_0_56, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(esk4_0,X1))=k4_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 1.18/1.36  cnf(c_0_57, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,X1),k4_xboole_0(X2,esk4_0))=k4_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_42])).
% 1.18/1.36  cnf(c_0_58, negated_conjecture, (~r1_tarski(k4_xboole_0(esk3_0,esk5_0),k4_xboole_0(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.18/1.36  cnf(c_0_59, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,X1),k4_xboole_0(esk4_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 1.18/1.36  cnf(c_0_60, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59])]), ['proof']).
% 1.18/1.36  # SZS output end CNFRefutation
% 1.18/1.36  # Proof object total steps             : 61
% 1.18/1.36  # Proof object clause steps            : 54
% 1.18/1.36  # Proof object formula steps           : 7
% 1.18/1.36  # Proof object conjectures             : 19
% 1.18/1.36  # Proof object clause conjectures      : 16
% 1.18/1.36  # Proof object formula conjectures     : 3
% 1.18/1.36  # Proof object initial clauses used    : 11
% 1.18/1.36  # Proof object initial formulas used   : 3
% 1.18/1.36  # Proof object generating inferences   : 42
% 1.18/1.36  # Proof object simplifying inferences  : 5
% 1.18/1.36  # Training examples: 0 positive, 0 negative
% 1.18/1.36  # Parsed axioms                        : 3
% 1.18/1.36  # Removed by relevancy pruning/SinE    : 0
% 1.18/1.36  # Initial clauses                      : 11
% 1.18/1.36  # Removed in clause preprocessing      : 0
% 1.18/1.36  # Initial clauses in saturation        : 11
% 1.18/1.36  # Processed clauses                    : 22122
% 1.18/1.36  # ...of these trivial                  : 417
% 1.18/1.36  # ...subsumed                          : 20783
% 1.18/1.36  # ...remaining for further processing  : 922
% 1.18/1.36  # Other redundant clauses eliminated   : 229
% 1.18/1.36  # Clauses deleted for lack of memory   : 0
% 1.18/1.36  # Backward-subsumed                    : 45
% 1.18/1.36  # Backward-rewritten                   : 5
% 1.18/1.36  # Generated clauses                    : 158570
% 1.18/1.36  # ...of the previous two non-trivial   : 127115
% 1.18/1.36  # Contextual simplify-reflections      : 8
% 1.18/1.36  # Paramodulations                      : 158151
% 1.18/1.36  # Factorizations                       : 94
% 1.18/1.36  # Equation resolutions                 : 325
% 1.18/1.36  # Propositional unsat checks           : 0
% 1.18/1.36  #    Propositional check models        : 0
% 1.18/1.36  #    Propositional check unsatisfiable : 0
% 1.18/1.36  #    Propositional clauses             : 0
% 1.18/1.36  #    Propositional clauses after purity: 0
% 1.18/1.36  #    Propositional unsat core size     : 0
% 1.18/1.36  #    Propositional preprocessing time  : 0.000
% 1.18/1.36  #    Propositional encoding time       : 0.000
% 1.18/1.36  #    Propositional solver time         : 0.000
% 1.18/1.36  #    Success case prop preproc time    : 0.000
% 1.18/1.36  #    Success case prop encoding time   : 0.000
% 1.18/1.36  #    Success case prop solver time     : 0.000
% 1.18/1.36  # Current number of processed clauses  : 872
% 1.18/1.36  #    Positive orientable unit clauses  : 129
% 1.18/1.36  #    Positive unorientable unit clauses: 2
% 1.18/1.36  #    Negative unit clauses             : 9
% 1.18/1.36  #    Non-unit-clauses                  : 732
% 1.18/1.36  # Current number of unprocessed clauses: 104970
% 1.18/1.36  # ...number of literals in the above   : 279812
% 1.18/1.36  # Current number of archived formulas  : 0
% 1.18/1.36  # Current number of archived clauses   : 50
% 1.18/1.36  # Clause-clause subsumption calls (NU) : 198775
% 1.18/1.36  # Rec. Clause-clause subsumption calls : 142184
% 1.18/1.36  # Non-unit clause-clause subsumptions  : 14705
% 1.18/1.36  # Unit Clause-clause subsumption calls : 1240
% 1.18/1.36  # Rewrite failures with RHS unbound    : 45
% 1.18/1.36  # BW rewrite match attempts            : 916
% 1.18/1.36  # BW rewrite match successes           : 15
% 1.18/1.36  # Condensation attempts                : 0
% 1.18/1.36  # Condensation successes               : 0
% 1.18/1.36  # Termbank termtop insertions          : 2347404
% 1.18/1.36  
% 1.18/1.36  # -------------------------------------------------
% 1.18/1.36  # User time                : 0.976 s
% 1.18/1.36  # System time              : 0.052 s
% 1.18/1.36  # Total time               : 1.029 s
% 1.18/1.36  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
