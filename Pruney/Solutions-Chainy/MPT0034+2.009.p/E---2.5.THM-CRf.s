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
% DateTime   : Thu Dec  3 10:31:57 EST 2020

% Result     : Theorem 1.47s
% Output     : CNFRefutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 127 expanded)
%              Number of clauses        :   33 (  65 expanded)
%              Number of leaves         :    3 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  110 ( 610 expanded)
%              Number of equality atoms :   18 ( 116 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t27_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).

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
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X4) )
       => r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)) ) ),
    inference(assume_negation,[status(cth)],[t27_xboole_1])).

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
    & r1_tarski(esk5_0,esk6_0)
    & ~ r1_tarski(k3_xboole_0(esk3_0,esk5_0),k3_xboole_0(esk4_0,esk6_0)) ),
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
    ( r1_tarski(esk5_0,esk6_0) ),
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
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
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
    ( r1_tarski(X1,esk6_0)
    | ~ r2_hidden(esk1_2(X1,esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X2)
    | r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k3_xboole_0(X2,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X3)
    | ~ r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_2(k3_xboole_0(X1,k3_xboole_0(X2,esk5_0)),X3),esk6_0)
    | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,esk5_0)),X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X1)
    | r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_13])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk2_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k3_xboole_0(X1,k3_xboole_0(X2,esk5_0)) = k3_xboole_0(X2,esk5_0)
    | r2_hidden(esk2_3(X1,k3_xboole_0(X2,esk5_0),k3_xboole_0(X2,esk5_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,esk5_0)),k3_xboole_0(X3,esk6_0))
    | ~ r2_hidden(esk1_2(k3_xboole_0(X1,k3_xboole_0(X2,esk5_0)),k3_xboole_0(X3,esk6_0)),X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_2(k3_xboole_0(esk3_0,X1),X2),esk4_0)
    | r1_tarski(k3_xboole_0(esk3_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( k3_xboole_0(esk6_0,k3_xboole_0(X1,esk5_0)) = k3_xboole_0(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_30,c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,k3_xboole_0(X1,esk5_0)),k3_xboole_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( k3_xboole_0(esk6_0,esk5_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(esk3_0,esk5_0),k3_xboole_0(esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:18:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.47/1.67  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 1.47/1.67  # and selection function SelectVGNonCR.
% 1.47/1.67  #
% 1.47/1.67  # Preprocessing time       : 0.027 s
% 1.47/1.67  # Presaturation interreduction done
% 1.47/1.67  
% 1.47/1.67  # Proof found!
% 1.47/1.67  # SZS status Theorem
% 1.47/1.67  # SZS output start CNFRefutation
% 1.47/1.67  fof(t27_xboole_1, conjecture, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_xboole_1)).
% 1.47/1.67  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.47/1.67  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.47/1.67  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))), inference(assume_negation,[status(cth)],[t27_xboole_1])).
% 1.47/1.67  fof(c_0_4, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.47/1.67  fof(c_0_5, negated_conjecture, ((r1_tarski(esk3_0,esk4_0)&r1_tarski(esk5_0,esk6_0))&~r1_tarski(k3_xboole_0(esk3_0,esk5_0),k3_xboole_0(esk4_0,esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 1.47/1.67  fof(c_0_6, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 1.47/1.67  cnf(c_0_7, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 1.47/1.67  cnf(c_0_8, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 1.47/1.67  cnf(c_0_9, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.47/1.67  cnf(c_0_10, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 1.47/1.67  cnf(c_0_11, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 1.47/1.67  cnf(c_0_12, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_9])).
% 1.47/1.67  cnf(c_0_13, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 1.47/1.67  cnf(c_0_14, negated_conjecture, (r1_tarski(X1,esk6_0)|~r2_hidden(esk1_2(X1,esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 1.47/1.67  cnf(c_0_15, plain, (r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X2)|r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 1.47/1.67  cnf(c_0_16, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.47/1.67  cnf(c_0_17, negated_conjecture, (r1_tarski(k3_xboole_0(X1,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 1.47/1.67  cnf(c_0_18, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.47/1.67  cnf(c_0_19, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.47/1.67  cnf(c_0_20, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_16])).
% 1.47/1.67  cnf(c_0_21, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,k3_xboole_0(X2,esk5_0))), inference(spm,[status(thm)],[c_0_7, c_0_17])).
% 1.47/1.67  cnf(c_0_22, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 1.47/1.67  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_18])).
% 1.47/1.67  cnf(c_0_24, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.47/1.67  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk2_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_19])).
% 1.47/1.67  cnf(c_0_26, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X3)|~r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_10, c_0_20])).
% 1.47/1.67  cnf(c_0_27, negated_conjecture, (r2_hidden(esk1_2(k3_xboole_0(X1,k3_xboole_0(X2,esk5_0)),X3),esk6_0)|r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,esk5_0)),X3)), inference(spm,[status(thm)],[c_0_21, c_0_15])).
% 1.47/1.67  cnf(c_0_28, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_7, c_0_22])).
% 1.47/1.67  cnf(c_0_29, plain, (r2_hidden(esk1_2(k3_xboole_0(X1,X2),X3),X1)|r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_23, c_0_13])).
% 1.47/1.67  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=X2|~r2_hidden(esk2_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_25])).
% 1.47/1.67  cnf(c_0_31, negated_conjecture, (k3_xboole_0(X1,k3_xboole_0(X2,esk5_0))=k3_xboole_0(X2,esk5_0)|r2_hidden(esk2_3(X1,k3_xboole_0(X2,esk5_0),k3_xboole_0(X2,esk5_0)),esk6_0)), inference(spm,[status(thm)],[c_0_21, c_0_25])).
% 1.47/1.67  cnf(c_0_32, negated_conjecture, (r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,esk5_0)),k3_xboole_0(X3,esk6_0))|~r2_hidden(esk1_2(k3_xboole_0(X1,k3_xboole_0(X2,esk5_0)),k3_xboole_0(X3,esk6_0)),X3)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 1.47/1.67  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_2(k3_xboole_0(esk3_0,X1),X2),esk4_0)|r1_tarski(k3_xboole_0(esk3_0,X1),X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 1.47/1.67  cnf(c_0_34, negated_conjecture, (k3_xboole_0(esk6_0,k3_xboole_0(X1,esk5_0))=k3_xboole_0(X1,esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 1.47/1.67  cnf(c_0_35, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_30, c_0_25])).
% 1.47/1.67  cnf(c_0_36, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,k3_xboole_0(X1,esk5_0)),k3_xboole_0(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 1.47/1.67  cnf(c_0_37, negated_conjecture, (k3_xboole_0(esk6_0,esk5_0)=esk5_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 1.47/1.67  cnf(c_0_38, negated_conjecture, (~r1_tarski(k3_xboole_0(esk3_0,esk5_0),k3_xboole_0(esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 1.47/1.67  cnf(c_0_39, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), ['proof']).
% 1.47/1.67  # SZS output end CNFRefutation
% 1.47/1.67  # Proof object total steps             : 40
% 1.47/1.67  # Proof object clause steps            : 33
% 1.47/1.67  # Proof object formula steps           : 7
% 1.47/1.67  # Proof object conjectures             : 19
% 1.47/1.67  # Proof object clause conjectures      : 16
% 1.47/1.67  # Proof object formula conjectures     : 3
% 1.47/1.67  # Proof object initial clauses used    : 11
% 1.47/1.67  # Proof object initial formulas used   : 3
% 1.47/1.67  # Proof object generating inferences   : 22
% 1.47/1.67  # Proof object simplifying inferences  : 2
% 1.47/1.67  # Training examples: 0 positive, 0 negative
% 1.47/1.67  # Parsed axioms                        : 3
% 1.47/1.67  # Removed by relevancy pruning/SinE    : 0
% 1.47/1.67  # Initial clauses                      : 12
% 1.47/1.67  # Removed in clause preprocessing      : 0
% 1.47/1.67  # Initial clauses in saturation        : 12
% 1.47/1.67  # Processed clauses                    : 8056
% 1.47/1.67  # ...of these trivial                  : 2294
% 1.47/1.67  # ...subsumed                          : 4440
% 1.47/1.67  # ...remaining for further processing  : 1322
% 1.47/1.67  # Other redundant clauses eliminated   : 3
% 1.47/1.67  # Clauses deleted for lack of memory   : 0
% 1.47/1.67  # Backward-subsumed                    : 4
% 1.47/1.67  # Backward-rewritten                   : 8
% 1.47/1.67  # Generated clauses                    : 233758
% 1.47/1.67  # ...of the previous two non-trivial   : 174848
% 1.47/1.67  # Contextual simplify-reflections      : 8
% 1.47/1.67  # Paramodulations                      : 233098
% 1.47/1.67  # Factorizations                       : 636
% 1.47/1.67  # Equation resolutions                 : 24
% 1.47/1.67  # Propositional unsat checks           : 0
% 1.47/1.67  #    Propositional check models        : 0
% 1.47/1.67  #    Propositional check unsatisfiable : 0
% 1.47/1.67  #    Propositional clauses             : 0
% 1.47/1.67  #    Propositional clauses after purity: 0
% 1.47/1.67  #    Propositional unsat core size     : 0
% 1.47/1.67  #    Propositional preprocessing time  : 0.000
% 1.47/1.67  #    Propositional encoding time       : 0.000
% 1.47/1.67  #    Propositional solver time         : 0.000
% 1.47/1.67  #    Success case prop preproc time    : 0.000
% 1.47/1.67  #    Success case prop encoding time   : 0.000
% 1.47/1.67  #    Success case prop solver time     : 0.000
% 1.47/1.67  # Current number of processed clauses  : 1298
% 1.47/1.67  #    Positive orientable unit clauses  : 407
% 1.47/1.67  #    Positive unorientable unit clauses: 0
% 1.47/1.67  #    Negative unit clauses             : 1
% 1.47/1.67  #    Non-unit-clauses                  : 890
% 1.47/1.67  # Current number of unprocessed clauses: 166810
% 1.47/1.67  # ...number of literals in the above   : 399199
% 1.47/1.67  # Current number of archived formulas  : 0
% 1.47/1.67  # Current number of archived clauses   : 24
% 1.47/1.67  # Clause-clause subsumption calls (NU) : 166589
% 1.47/1.67  # Rec. Clause-clause subsumption calls : 109285
% 1.47/1.67  # Non-unit clause-clause subsumptions  : 4452
% 1.47/1.67  # Unit Clause-clause subsumption calls : 16471
% 1.47/1.67  # Rewrite failures with RHS unbound    : 0
% 1.47/1.67  # BW rewrite match attempts            : 13795
% 1.47/1.67  # BW rewrite match successes           : 8
% 1.47/1.67  # Condensation attempts                : 0
% 1.47/1.67  # Condensation successes               : 0
% 1.47/1.67  # Termbank termtop insertions          : 3547093
% 1.47/1.68  
% 1.47/1.68  # -------------------------------------------------
% 1.47/1.68  # User time                : 1.236 s
% 1.47/1.68  # System time              : 0.097 s
% 1.47/1.68  # Total time               : 1.333 s
% 1.47/1.68  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
