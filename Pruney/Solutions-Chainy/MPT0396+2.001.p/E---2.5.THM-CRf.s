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
% DateTime   : Thu Dec  3 10:47:23 EST 2020

% Result     : Theorem 28.35s
% Output     : CNFRefutation 28.35s
% Verified   : 
% Statistics : Number of formulae       :   36 (  71 expanded)
%              Number of clauses        :   27 (  34 expanded)
%              Number of leaves         :    4 (  17 expanded)
%              Depth                    :   14
%              Number of atoms          :  124 ( 308 expanded)
%              Number of equality atoms :   12 (  34 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(d2_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
    <=> ! [X3] :
          ~ ( r2_hidden(X3,X1)
            & ! [X4] :
                ~ ( r2_hidden(X4,X2)
                  & r1_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t18_setfam_1,conjecture,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

fof(c_0_4,plain,(
    ! [X11,X12,X13,X15,X16,X17,X18,X20] :
      ( ( r2_hidden(X13,esk2_3(X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k3_tarski(X11) )
      & ( r2_hidden(esk2_3(X11,X12,X13),X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k3_tarski(X11) )
      & ( ~ r2_hidden(X15,X16)
        | ~ r2_hidden(X16,X11)
        | r2_hidden(X15,X12)
        | X12 != k3_tarski(X11) )
      & ( ~ r2_hidden(esk3_2(X17,X18),X18)
        | ~ r2_hidden(esk3_2(X17,X18),X20)
        | ~ r2_hidden(X20,X17)
        | X18 = k3_tarski(X17) )
      & ( r2_hidden(esk3_2(X17,X18),esk4_2(X17,X18))
        | r2_hidden(esk3_2(X17,X18),X18)
        | X18 = k3_tarski(X17) )
      & ( r2_hidden(esk4_2(X17,X18),X17)
        | r2_hidden(esk3_2(X17,X18),X18)
        | X18 = k3_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_5,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_6,plain,(
    ! [X22,X23,X24,X26,X27,X29] :
      ( ( r2_hidden(esk5_3(X22,X23,X24),X23)
        | ~ r2_hidden(X24,X22)
        | ~ r1_setfam_1(X22,X23) )
      & ( r1_tarski(X24,esk5_3(X22,X23,X24))
        | ~ r2_hidden(X24,X22)
        | ~ r1_setfam_1(X22,X23) )
      & ( r2_hidden(esk6_2(X26,X27),X26)
        | r1_setfam_1(X26,X27) )
      & ( ~ r2_hidden(X29,X27)
        | ~ r1_tarski(esk6_2(X26,X27),X29)
        | r1_setfam_1(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

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

cnf(c_0_10,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r1_setfam_1(X3,X2)
    | ~ r2_hidden(X1,esk5_3(X3,X2,X4))
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_setfam_1(X1,X2)
       => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    inference(assume_negation,[status(cth)],[t18_setfam_1])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_2(esk5_3(X1,X2,X3),X4),k3_tarski(X2))
    | r1_tarski(esk5_3(X1,X2,X3),X4)
    | ~ r1_setfam_1(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_15,negated_conjecture,
    ( r1_setfam_1(esk7_0,esk8_0)
    & ~ r1_tarski(k3_tarski(esk7_0),k3_tarski(esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_16,plain,
    ( r1_tarski(esk5_3(X1,X2,X3),k3_tarski(X2))
    | ~ r1_setfam_1(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( r1_setfam_1(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,esk5_3(X2,X3,X1))
    | ~ r2_hidden(X1,X2)
    | ~ r1_setfam_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk5_3(esk7_0,esk8_0,X1),k3_tarski(esk8_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(X1,esk5_3(esk7_0,esk8_0,X1))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk5_3(esk7_0,esk8_0,esk2_3(esk7_0,X1,X2)),k3_tarski(esk8_0))
    | X1 != k3_tarski(esk7_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk2_3(esk7_0,X1,X2),esk5_3(esk7_0,esk8_0,esk2_3(esk7_0,X1,X2)))
    | X1 != k3_tarski(esk7_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk5_3(esk7_0,esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),X1)),k3_tarski(esk8_0))
    | ~ r2_hidden(X1,k3_tarski(esk7_0)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),X1),esk5_3(esk7_0,esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),X1)))
    | ~ r2_hidden(X1,k3_tarski(esk7_0)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_26,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk5_3(esk7_0,esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk1_2(k3_tarski(esk7_0),X1))),k3_tarski(esk8_0))
    | r1_tarski(k3_tarski(esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk1_2(k3_tarski(esk7_0),X1)),esk5_3(esk7_0,esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk1_2(k3_tarski(esk7_0),X1))))
    | r1_tarski(k3_tarski(esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,k3_tarski(esk8_0))
    | r1_tarski(k3_tarski(esk7_0),X2)
    | ~ r2_hidden(X1,esk5_3(esk7_0,esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk1_2(k3_tarski(esk7_0),X2)))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,esk5_3(esk7_0,esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk1_2(k3_tarski(esk7_0),X2))))
    | r1_tarski(k3_tarski(esk7_0),X2)
    | ~ r2_hidden(X1,esk2_3(esk7_0,k3_tarski(esk7_0),esk1_2(k3_tarski(esk7_0),X2))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,k3_tarski(esk8_0))
    | r1_tarski(k3_tarski(esk7_0),X2)
    | ~ r2_hidden(X1,esk2_3(esk7_0,k3_tarski(esk7_0),esk1_2(k3_tarski(esk7_0),X2))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_2(k3_tarski(esk7_0),X1),k3_tarski(esk8_0))
    | r1_tarski(k3_tarski(esk7_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_11])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(esk7_0),k3_tarski(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_33]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 28.35/28.55  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 28.35/28.55  # and selection function SelectVGNonCR.
% 28.35/28.55  #
% 28.35/28.55  # Preprocessing time       : 0.027 s
% 28.35/28.55  # Presaturation interreduction done
% 28.35/28.55  
% 28.35/28.55  # Proof found!
% 28.35/28.55  # SZS status Theorem
% 28.35/28.55  # SZS output start CNFRefutation
% 28.35/28.55  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 28.35/28.55  fof(d2_setfam_1, axiom, ![X1, X2]:(r1_setfam_1(X1,X2)<=>![X3]:~((r2_hidden(X3,X1)&![X4]:~((r2_hidden(X4,X2)&r1_tarski(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 28.35/28.55  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 28.35/28.55  fof(t18_setfam_1, conjecture, ![X1, X2]:(r1_setfam_1(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_setfam_1)).
% 28.35/28.55  fof(c_0_4, plain, ![X11, X12, X13, X15, X16, X17, X18, X20]:((((r2_hidden(X13,esk2_3(X11,X12,X13))|~r2_hidden(X13,X12)|X12!=k3_tarski(X11))&(r2_hidden(esk2_3(X11,X12,X13),X11)|~r2_hidden(X13,X12)|X12!=k3_tarski(X11)))&(~r2_hidden(X15,X16)|~r2_hidden(X16,X11)|r2_hidden(X15,X12)|X12!=k3_tarski(X11)))&((~r2_hidden(esk3_2(X17,X18),X18)|(~r2_hidden(esk3_2(X17,X18),X20)|~r2_hidden(X20,X17))|X18=k3_tarski(X17))&((r2_hidden(esk3_2(X17,X18),esk4_2(X17,X18))|r2_hidden(esk3_2(X17,X18),X18)|X18=k3_tarski(X17))&(r2_hidden(esk4_2(X17,X18),X17)|r2_hidden(esk3_2(X17,X18),X18)|X18=k3_tarski(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 28.35/28.55  cnf(c_0_5, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 28.35/28.55  fof(c_0_6, plain, ![X22, X23, X24, X26, X27, X29]:(((r2_hidden(esk5_3(X22,X23,X24),X23)|~r2_hidden(X24,X22)|~r1_setfam_1(X22,X23))&(r1_tarski(X24,esk5_3(X22,X23,X24))|~r2_hidden(X24,X22)|~r1_setfam_1(X22,X23)))&((r2_hidden(esk6_2(X26,X27),X26)|r1_setfam_1(X26,X27))&(~r2_hidden(X29,X27)|~r1_tarski(esk6_2(X26,X27),X29)|r1_setfam_1(X26,X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).
% 28.35/28.55  cnf(c_0_7, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_5])).
% 28.35/28.55  cnf(c_0_8, plain, (r2_hidden(esk5_3(X1,X2,X3),X2)|~r2_hidden(X3,X1)|~r1_setfam_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 28.35/28.55  fof(c_0_9, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 28.35/28.55  cnf(c_0_10, plain, (r2_hidden(X1,k3_tarski(X2))|~r1_setfam_1(X3,X2)|~r2_hidden(X1,esk5_3(X3,X2,X4))|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 28.35/28.55  cnf(c_0_11, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 28.35/28.55  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(r1_setfam_1(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2)))), inference(assume_negation,[status(cth)],[t18_setfam_1])).
% 28.35/28.55  cnf(c_0_13, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 28.35/28.55  cnf(c_0_14, plain, (r2_hidden(esk1_2(esk5_3(X1,X2,X3),X4),k3_tarski(X2))|r1_tarski(esk5_3(X1,X2,X3),X4)|~r1_setfam_1(X1,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 28.35/28.55  fof(c_0_15, negated_conjecture, (r1_setfam_1(esk7_0,esk8_0)&~r1_tarski(k3_tarski(esk7_0),k3_tarski(esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 28.35/28.55  cnf(c_0_16, plain, (r1_tarski(esk5_3(X1,X2,X3),k3_tarski(X2))|~r1_setfam_1(X1,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 28.35/28.55  cnf(c_0_17, negated_conjecture, (r1_setfam_1(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 28.35/28.55  cnf(c_0_18, plain, (r1_tarski(X1,esk5_3(X2,X3,X1))|~r2_hidden(X1,X2)|~r1_setfam_1(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 28.35/28.55  cnf(c_0_19, negated_conjecture, (r1_tarski(esk5_3(esk7_0,esk8_0,X1),k3_tarski(esk8_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 28.35/28.55  cnf(c_0_20, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 28.35/28.55  cnf(c_0_21, negated_conjecture, (r1_tarski(X1,esk5_3(esk7_0,esk8_0,X1))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_18, c_0_17])).
% 28.35/28.55  cnf(c_0_22, negated_conjecture, (r1_tarski(esk5_3(esk7_0,esk8_0,esk2_3(esk7_0,X1,X2)),k3_tarski(esk8_0))|X1!=k3_tarski(esk7_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 28.35/28.55  cnf(c_0_23, negated_conjecture, (r1_tarski(esk2_3(esk7_0,X1,X2),esk5_3(esk7_0,esk8_0,esk2_3(esk7_0,X1,X2)))|X1!=k3_tarski(esk7_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_21, c_0_20])).
% 28.35/28.55  cnf(c_0_24, negated_conjecture, (r1_tarski(esk5_3(esk7_0,esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),X1)),k3_tarski(esk8_0))|~r2_hidden(X1,k3_tarski(esk7_0))), inference(er,[status(thm)],[c_0_22])).
% 28.35/28.55  cnf(c_0_25, negated_conjecture, (r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),X1),esk5_3(esk7_0,esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),X1)))|~r2_hidden(X1,k3_tarski(esk7_0))), inference(er,[status(thm)],[c_0_23])).
% 28.35/28.55  cnf(c_0_26, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 28.35/28.55  cnf(c_0_27, negated_conjecture, (r1_tarski(esk5_3(esk7_0,esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk1_2(k3_tarski(esk7_0),X1))),k3_tarski(esk8_0))|r1_tarski(k3_tarski(esk7_0),X1)), inference(spm,[status(thm)],[c_0_24, c_0_11])).
% 28.35/28.55  cnf(c_0_28, negated_conjecture, (r1_tarski(esk2_3(esk7_0,k3_tarski(esk7_0),esk1_2(k3_tarski(esk7_0),X1)),esk5_3(esk7_0,esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk1_2(k3_tarski(esk7_0),X1))))|r1_tarski(k3_tarski(esk7_0),X1)), inference(spm,[status(thm)],[c_0_25, c_0_11])).
% 28.35/28.55  cnf(c_0_29, negated_conjecture, (r2_hidden(X1,k3_tarski(esk8_0))|r1_tarski(k3_tarski(esk7_0),X2)|~r2_hidden(X1,esk5_3(esk7_0,esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk1_2(k3_tarski(esk7_0),X2))))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 28.35/28.55  cnf(c_0_30, negated_conjecture, (r2_hidden(X1,esk5_3(esk7_0,esk8_0,esk2_3(esk7_0,k3_tarski(esk7_0),esk1_2(k3_tarski(esk7_0),X2))))|r1_tarski(k3_tarski(esk7_0),X2)|~r2_hidden(X1,esk2_3(esk7_0,k3_tarski(esk7_0),esk1_2(k3_tarski(esk7_0),X2)))), inference(spm,[status(thm)],[c_0_26, c_0_28])).
% 28.35/28.55  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,k3_tarski(esk8_0))|r1_tarski(k3_tarski(esk7_0),X2)|~r2_hidden(X1,esk2_3(esk7_0,k3_tarski(esk7_0),esk1_2(k3_tarski(esk7_0),X2)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 28.35/28.55  cnf(c_0_32, plain, (r2_hidden(X1,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k3_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 28.35/28.55  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_2(k3_tarski(esk7_0),X1),k3_tarski(esk8_0))|r1_tarski(k3_tarski(esk7_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_11])).
% 28.35/28.55  cnf(c_0_34, negated_conjecture, (~r1_tarski(k3_tarski(esk7_0),k3_tarski(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 28.35/28.55  cnf(c_0_35, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_33]), c_0_34]), ['proof']).
% 28.35/28.55  # SZS output end CNFRefutation
% 28.35/28.55  # Proof object total steps             : 36
% 28.35/28.55  # Proof object clause steps            : 27
% 28.35/28.55  # Proof object formula steps           : 9
% 28.35/28.55  # Proof object conjectures             : 18
% 28.35/28.55  # Proof object clause conjectures      : 15
% 28.35/28.55  # Proof object formula conjectures     : 3
% 28.35/28.55  # Proof object initial clauses used    : 10
% 28.35/28.55  # Proof object initial formulas used   : 4
% 28.35/28.55  # Proof object generating inferences   : 17
% 28.35/28.55  # Proof object simplifying inferences  : 2
% 28.35/28.55  # Training examples: 0 positive, 0 negative
% 28.35/28.55  # Parsed axioms                        : 4
% 28.35/28.55  # Removed by relevancy pruning/SinE    : 0
% 28.35/28.55  # Initial clauses                      : 15
% 28.35/28.55  # Removed in clause preprocessing      : 0
% 28.35/28.55  # Initial clauses in saturation        : 15
% 28.35/28.55  # Processed clauses                    : 15063
% 28.35/28.55  # ...of these trivial                  : 0
% 28.35/28.55  # ...subsumed                          : 3807
% 28.35/28.55  # ...remaining for further processing  : 11256
% 28.35/28.55  # Other redundant clauses eliminated   : 0
% 28.35/28.55  # Clauses deleted for lack of memory   : 9179
% 28.35/28.55  # Backward-subsumed                    : 156
% 28.35/28.55  # Backward-rewritten                   : 3
% 28.35/28.55  # Generated clauses                    : 3280472
% 28.35/28.55  # ...of the previous two non-trivial   : 3273321
% 28.35/28.55  # Contextual simplify-reflections      : 131
% 28.35/28.55  # Paramodulations                      : 3279630
% 28.35/28.55  # Factorizations                       : 530
% 28.35/28.55  # Equation resolutions                 : 312
% 28.35/28.55  # Propositional unsat checks           : 0
% 28.35/28.55  #    Propositional check models        : 0
% 28.35/28.55  #    Propositional check unsatisfiable : 0
% 28.35/28.55  #    Propositional clauses             : 0
% 28.35/28.55  #    Propositional clauses after purity: 0
% 28.35/28.55  #    Propositional unsat core size     : 0
% 28.35/28.55  #    Propositional preprocessing time  : 0.000
% 28.35/28.55  #    Propositional encoding time       : 0.000
% 28.35/28.55  #    Propositional solver time         : 0.000
% 28.35/28.55  #    Success case prop preproc time    : 0.000
% 28.35/28.55  #    Success case prop encoding time   : 0.000
% 28.35/28.55  #    Success case prop solver time     : 0.000
% 28.35/28.55  # Current number of processed clauses  : 11082
% 28.35/28.55  #    Positive orientable unit clauses  : 12
% 28.35/28.55  #    Positive unorientable unit clauses: 0
% 28.35/28.55  #    Negative unit clauses             : 1
% 28.35/28.55  #    Non-unit-clauses                  : 11069
% 28.35/28.55  # Current number of unprocessed clauses: 2162881
% 28.35/28.55  # ...number of literals in the above   : 12756753
% 28.35/28.55  # Current number of archived formulas  : 0
% 28.35/28.55  # Current number of archived clauses   : 174
% 28.35/28.55  # Clause-clause subsumption calls (NU) : 7555451
% 28.35/28.55  # Rec. Clause-clause subsumption calls : 690994
% 28.35/28.55  # Non-unit clause-clause subsumptions  : 4094
% 28.35/28.55  # Unit Clause-clause subsumption calls : 17252
% 28.35/28.55  # Rewrite failures with RHS unbound    : 0
% 28.35/28.55  # BW rewrite match attempts            : 121
% 28.35/28.55  # BW rewrite match successes           : 3
% 28.35/28.55  # Condensation attempts                : 0
% 28.35/28.55  # Condensation successes               : 0
% 28.35/28.55  # Termbank termtop insertions          : 105863943
% 28.42/28.63  
% 28.42/28.63  # -------------------------------------------------
% 28.42/28.63  # User time                : 27.407 s
% 28.42/28.63  # System time              : 0.877 s
% 28.42/28.63  # Total time               : 28.284 s
% 28.42/28.63  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
