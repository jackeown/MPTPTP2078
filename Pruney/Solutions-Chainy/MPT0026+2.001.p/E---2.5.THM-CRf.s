%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:52 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   37 (  82 expanded)
%              Number of clauses        :   30 (  40 expanded)
%              Number of leaves         :    3 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :  108 ( 358 expanded)
%              Number of equality atoms :   17 (  54 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t19_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X1,X3) )
       => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    inference(assume_negation,[status(cth)],[t19_xboole_1])).

fof(c_0_4,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_5,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    & r1_tarski(esk3_0,esk5_0)
    & ~ r1_tarski(esk3_0,k3_xboole_0(esk4_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

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

cnf(c_0_7,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( r1_tarski(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(X1,esk5_0)
    | ~ r2_hidden(esk1_2(X1,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X2)
    | r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk3_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( esk3_0 = k3_xboole_0(X1,X2)
    | r2_hidden(esk2_3(X1,X2,esk3_0),esk4_0)
    | r2_hidden(esk2_3(X1,X2,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k3_xboole_0(X2,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_20])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk2_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( esk3_0 = k3_xboole_0(esk4_0,X1)
    | r2_hidden(esk2_3(esk4_0,X1,esk3_0),esk4_0) ),
    inference(ef,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_2(k3_xboole_0(X1,esk3_0),X2),esk5_0)
    | r1_tarski(k3_xboole_0(X1,esk3_0),X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X3)
    | ~ r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),esk5_0)
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk3_0,k3_xboole_0(X1,esk5_0))
    | ~ r2_hidden(esk1_2(esk3_0,k3_xboole_0(X1,esk5_0)),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),esk4_0)
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k3_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n023.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 20:24:35 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.41  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.12/0.41  # and selection function SelectVGNonCR.
% 0.12/0.41  #
% 0.12/0.41  # Preprocessing time       : 0.026 s
% 0.12/0.41  # Presaturation interreduction done
% 0.12/0.41  
% 0.12/0.41  # Proof found!
% 0.12/0.41  # SZS status Theorem
% 0.12/0.41  # SZS output start CNFRefutation
% 0.12/0.41  fof(t19_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.12/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.41  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.12/0.41  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3)))), inference(assume_negation,[status(cth)],[t19_xboole_1])).
% 0.12/0.41  fof(c_0_4, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.41  fof(c_0_5, negated_conjecture, ((r1_tarski(esk3_0,esk4_0)&r1_tarski(esk3_0,esk5_0))&~r1_tarski(esk3_0,k3_xboole_0(esk4_0,esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.12/0.41  fof(c_0_6, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.12/0.41  cnf(c_0_7, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.41  cnf(c_0_8, negated_conjecture, (r1_tarski(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.41  cnf(c_0_9, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.41  cnf(c_0_10, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.41  cnf(c_0_11, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.12/0.41  cnf(c_0_12, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_9])).
% 0.12/0.41  cnf(c_0_13, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.41  cnf(c_0_14, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.41  cnf(c_0_15, negated_conjecture, (r1_tarski(X1,esk5_0)|~r2_hidden(esk1_2(X1,esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.12/0.41  cnf(c_0_16, plain, (r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X2)|r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.12/0.41  cnf(c_0_17, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.41  cnf(c_0_18, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_7, c_0_14])).
% 0.12/0.41  cnf(c_0_19, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.41  cnf(c_0_20, negated_conjecture, (r1_tarski(k3_xboole_0(X1,esk3_0),esk5_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.12/0.41  cnf(c_0_21, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.41  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk2_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_17])).
% 0.12/0.41  cnf(c_0_23, negated_conjecture, (esk3_0=k3_xboole_0(X1,X2)|r2_hidden(esk2_3(X1,X2,esk3_0),esk4_0)|r2_hidden(esk2_3(X1,X2,esk3_0),X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.41  cnf(c_0_24, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.41  cnf(c_0_25, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k3_xboole_0(X2,esk3_0))), inference(spm,[status(thm)],[c_0_7, c_0_20])).
% 0.12/0.41  cnf(c_0_26, plain, (k3_xboole_0(X1,X2)=X2|~r2_hidden(esk2_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_22])).
% 0.12/0.41  cnf(c_0_27, negated_conjecture, (esk3_0=k3_xboole_0(esk4_0,X1)|r2_hidden(esk2_3(esk4_0,X1,esk3_0),esk4_0)), inference(ef,[status(thm)],[c_0_23])).
% 0.12/0.41  cnf(c_0_28, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_24])).
% 0.12/0.41  cnf(c_0_29, negated_conjecture, (r2_hidden(esk1_2(k3_xboole_0(X1,esk3_0),X2),esk5_0)|r1_tarski(k3_xboole_0(X1,esk3_0),X2)), inference(spm,[status(thm)],[c_0_25, c_0_13])).
% 0.12/0.41  cnf(c_0_30, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.41  cnf(c_0_31, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X3)|~r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_10, c_0_28])).
% 0.12/0.41  cnf(c_0_32, negated_conjecture, (r2_hidden(esk1_2(esk3_0,X1),esk5_0)|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.41  cnf(c_0_33, negated_conjecture, (r1_tarski(esk3_0,k3_xboole_0(X1,esk5_0))|~r2_hidden(esk1_2(esk3_0,k3_xboole_0(X1,esk5_0)),X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.12/0.41  cnf(c_0_34, negated_conjecture, (r2_hidden(esk1_2(esk3_0,X1),esk4_0)|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_18, c_0_13])).
% 0.12/0.41  cnf(c_0_35, negated_conjecture, (~r1_tarski(esk3_0,k3_xboole_0(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.41  cnf(c_0_36, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), ['proof']).
% 0.12/0.41  # SZS output end CNFRefutation
% 0.12/0.41  # Proof object total steps             : 37
% 0.12/0.41  # Proof object clause steps            : 30
% 0.12/0.41  # Proof object formula steps           : 7
% 0.12/0.41  # Proof object conjectures             : 19
% 0.12/0.41  # Proof object clause conjectures      : 16
% 0.12/0.41  # Proof object formula conjectures     : 3
% 0.12/0.41  # Proof object initial clauses used    : 11
% 0.12/0.41  # Proof object initial formulas used   : 3
% 0.12/0.41  # Proof object generating inferences   : 19
% 0.12/0.41  # Proof object simplifying inferences  : 2
% 0.12/0.41  # Training examples: 0 positive, 0 negative
% 0.12/0.41  # Parsed axioms                        : 3
% 0.12/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.41  # Initial clauses                      : 12
% 0.12/0.41  # Removed in clause preprocessing      : 0
% 0.12/0.41  # Initial clauses in saturation        : 12
% 0.12/0.41  # Processed clauses                    : 761
% 0.12/0.41  # ...of these trivial                  : 37
% 0.12/0.41  # ...subsumed                          : 504
% 0.12/0.41  # ...remaining for further processing  : 220
% 0.12/0.41  # Other redundant clauses eliminated   : 3
% 0.12/0.41  # Clauses deleted for lack of memory   : 0
% 0.12/0.41  # Backward-subsumed                    : 0
% 0.12/0.41  # Backward-rewritten                   : 0
% 0.12/0.41  # Generated clauses                    : 4673
% 0.12/0.41  # ...of the previous two non-trivial   : 4069
% 0.12/0.41  # Contextual simplify-reflections      : 2
% 0.12/0.41  # Paramodulations                      : 4561
% 0.12/0.41  # Factorizations                       : 100
% 0.12/0.41  # Equation resolutions                 : 12
% 0.12/0.41  # Propositional unsat checks           : 0
% 0.12/0.41  #    Propositional check models        : 0
% 0.12/0.41  #    Propositional check unsatisfiable : 0
% 0.12/0.41  #    Propositional clauses             : 0
% 0.12/0.41  #    Propositional clauses after purity: 0
% 0.12/0.41  #    Propositional unsat core size     : 0
% 0.12/0.41  #    Propositional preprocessing time  : 0.000
% 0.12/0.41  #    Propositional encoding time       : 0.000
% 0.12/0.41  #    Propositional solver time         : 0.000
% 0.12/0.41  #    Success case prop preproc time    : 0.000
% 0.12/0.41  #    Success case prop encoding time   : 0.000
% 0.12/0.41  #    Success case prop solver time     : 0.000
% 0.12/0.41  # Current number of processed clauses  : 208
% 0.12/0.41  #    Positive orientable unit clauses  : 45
% 0.12/0.41  #    Positive unorientable unit clauses: 0
% 0.12/0.41  #    Negative unit clauses             : 1
% 0.12/0.41  #    Non-unit-clauses                  : 162
% 0.12/0.41  # Current number of unprocessed clauses: 3327
% 0.12/0.41  # ...number of literals in the above   : 8961
% 0.12/0.41  # Current number of archived formulas  : 0
% 0.12/0.41  # Current number of archived clauses   : 12
% 0.12/0.41  # Clause-clause subsumption calls (NU) : 6762
% 0.12/0.41  # Rec. Clause-clause subsumption calls : 4796
% 0.12/0.41  # Non-unit clause-clause subsumptions  : 506
% 0.12/0.41  # Unit Clause-clause subsumption calls : 496
% 0.12/0.41  # Rewrite failures with RHS unbound    : 0
% 0.12/0.41  # BW rewrite match attempts            : 115
% 0.12/0.41  # BW rewrite match successes           : 0
% 0.12/0.41  # Condensation attempts                : 0
% 0.12/0.41  # Condensation successes               : 0
% 0.12/0.41  # Termbank termtop insertions          : 63948
% 0.12/0.41  
% 0.12/0.41  # -------------------------------------------------
% 0.12/0.41  # User time                : 0.081 s
% 0.12/0.41  # System time              : 0.007 s
% 0.12/0.41  # Total time               : 0.088 s
% 0.12/0.41  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
