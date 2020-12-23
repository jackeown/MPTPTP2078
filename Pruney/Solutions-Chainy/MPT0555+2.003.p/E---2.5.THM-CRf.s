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
% DateTime   : Thu Dec  3 10:51:02 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   28 (  59 expanded)
%              Number of clauses        :   19 (  24 expanded)
%              Number of leaves         :    4 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :  109 ( 236 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t157_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X4),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( r1_tarski(X2,X3)
             => r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t157_relat_1])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_relat_1(esk8_0)
    & r1_tarski(esk7_0,esk8_0)
    & ~ r1_tarski(k9_relat_1(esk7_0,esk6_0),k9_relat_1(esk8_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_7,plain,(
    ! [X12,X13,X14,X15,X17,X18,X19,X20,X22] :
      ( ( r2_hidden(k4_tarski(esk2_4(X12,X13,X14,X15),X15),X12)
        | ~ r2_hidden(X15,X14)
        | X14 != k9_relat_1(X12,X13)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(esk2_4(X12,X13,X14,X15),X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k9_relat_1(X12,X13)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(k4_tarski(X18,X17),X12)
        | ~ r2_hidden(X18,X13)
        | r2_hidden(X17,X14)
        | X14 != k9_relat_1(X12,X13)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(esk3_3(X12,X19,X20),X20)
        | ~ r2_hidden(k4_tarski(X22,esk3_3(X12,X19,X20)),X12)
        | ~ r2_hidden(X22,X19)
        | X20 = k9_relat_1(X12,X19)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(esk4_3(X12,X19,X20),esk3_3(X12,X19,X20)),X12)
        | r2_hidden(esk3_3(X12,X19,X20),X20)
        | X20 = k9_relat_1(X12,X19)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(esk4_3(X12,X19,X20),X19)
        | r2_hidden(esk3_3(X12,X19,X20),X20)
        | X20 = k9_relat_1(X12,X19)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).

fof(c_0_8,plain,(
    ! [X24,X25,X26,X28] :
      ( ( r2_hidden(esk5_3(X24,X25,X26),k1_relat_1(X26))
        | ~ r2_hidden(X24,k9_relat_1(X26,X25))
        | ~ v1_relat_1(X26) )
      & ( r2_hidden(k4_tarski(esk5_3(X24,X25,X26),X24),X26)
        | ~ r2_hidden(X24,k9_relat_1(X26,X25))
        | ~ v1_relat_1(X26) )
      & ( r2_hidden(esk5_3(X24,X25,X26),X25)
        | ~ r2_hidden(X24,k9_relat_1(X26,X25))
        | ~ v1_relat_1(X26) )
      & ( ~ r2_hidden(X28,k1_relat_1(X26))
        | ~ r2_hidden(k4_tarski(X28,X24),X26)
        | ~ r2_hidden(X28,X25)
        | r2_hidden(X24,k9_relat_1(X26,X25))
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_9,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk7_0,esk6_0),k9_relat_1(esk8_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(X2,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X5 != k9_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk1_2(k9_relat_1(esk7_0,esk6_0),k9_relat_1(esk8_0,esk6_0)),k9_relat_1(esk7_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,X1),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_2(k9_relat_1(esk7_0,esk6_0),k9_relat_1(esk8_0,esk6_0)),esk6_0,esk7_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(esk1_2(k9_relat_1(esk7_0,esk6_0),k9_relat_1(esk8_0,esk6_0)),esk6_0,esk7_0),esk1_2(k9_relat_1(esk7_0,esk6_0),k9_relat_1(esk8_0,esk6_0))),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_13]),c_0_14])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,k9_relat_1(X2,esk6_0))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(esk5_3(esk1_2(k9_relat_1(esk7_0,esk6_0),k9_relat_1(esk8_0,esk6_0)),esk6_0,esk7_0),X1),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(esk1_2(k9_relat_1(esk7_0,esk6_0),k9_relat_1(esk8_0,esk6_0)),esk6_0,esk7_0),esk1_2(k9_relat_1(esk7_0,esk6_0),k9_relat_1(esk8_0,esk6_0))),esk8_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_2(k9_relat_1(esk7_0,esk6_0),k9_relat_1(esk8_0,esk6_0)),k9_relat_1(esk8_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_9]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:36:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.14/0.38  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t157_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_relat_1)).
% 0.14/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.38  fof(d13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X5,X4),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_relat_1)).
% 0.14/0.38  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.14/0.38  fof(c_0_4, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1)))))), inference(assume_negation,[status(cth)],[t157_relat_1])).
% 0.14/0.38  fof(c_0_5, negated_conjecture, (v1_relat_1(esk7_0)&(v1_relat_1(esk8_0)&(r1_tarski(esk7_0,esk8_0)&~r1_tarski(k9_relat_1(esk7_0,esk6_0),k9_relat_1(esk8_0,esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.14/0.38  fof(c_0_6, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.38  fof(c_0_7, plain, ![X12, X13, X14, X15, X17, X18, X19, X20, X22]:((((r2_hidden(k4_tarski(esk2_4(X12,X13,X14,X15),X15),X12)|~r2_hidden(X15,X14)|X14!=k9_relat_1(X12,X13)|~v1_relat_1(X12))&(r2_hidden(esk2_4(X12,X13,X14,X15),X13)|~r2_hidden(X15,X14)|X14!=k9_relat_1(X12,X13)|~v1_relat_1(X12)))&(~r2_hidden(k4_tarski(X18,X17),X12)|~r2_hidden(X18,X13)|r2_hidden(X17,X14)|X14!=k9_relat_1(X12,X13)|~v1_relat_1(X12)))&((~r2_hidden(esk3_3(X12,X19,X20),X20)|(~r2_hidden(k4_tarski(X22,esk3_3(X12,X19,X20)),X12)|~r2_hidden(X22,X19))|X20=k9_relat_1(X12,X19)|~v1_relat_1(X12))&((r2_hidden(k4_tarski(esk4_3(X12,X19,X20),esk3_3(X12,X19,X20)),X12)|r2_hidden(esk3_3(X12,X19,X20),X20)|X20=k9_relat_1(X12,X19)|~v1_relat_1(X12))&(r2_hidden(esk4_3(X12,X19,X20),X19)|r2_hidden(esk3_3(X12,X19,X20),X20)|X20=k9_relat_1(X12,X19)|~v1_relat_1(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).
% 0.14/0.38  fof(c_0_8, plain, ![X24, X25, X26, X28]:((((r2_hidden(esk5_3(X24,X25,X26),k1_relat_1(X26))|~r2_hidden(X24,k9_relat_1(X26,X25))|~v1_relat_1(X26))&(r2_hidden(k4_tarski(esk5_3(X24,X25,X26),X24),X26)|~r2_hidden(X24,k9_relat_1(X26,X25))|~v1_relat_1(X26)))&(r2_hidden(esk5_3(X24,X25,X26),X25)|~r2_hidden(X24,k9_relat_1(X26,X25))|~v1_relat_1(X26)))&(~r2_hidden(X28,k1_relat_1(X26))|~r2_hidden(k4_tarski(X28,X24),X26)|~r2_hidden(X28,X25)|r2_hidden(X24,k9_relat_1(X26,X25))|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.14/0.38  cnf(c_0_9, negated_conjecture, (~r1_tarski(k9_relat_1(esk7_0,esk6_0),k9_relat_1(esk8_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.38  cnf(c_0_10, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_11, plain, (r2_hidden(X2,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X5!=k9_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_12, plain, (r2_hidden(esk5_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_13, negated_conjecture, (r2_hidden(esk1_2(k9_relat_1(esk7_0,esk6_0),k9_relat_1(esk8_0,esk6_0)),k9_relat_1(esk7_0,esk6_0))), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.14/0.38  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.38  cnf(c_0_15, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (r1_tarski(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.38  cnf(c_0_17, plain, (r2_hidden(k4_tarski(esk5_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_18, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X4,X1),X2)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (r2_hidden(esk5_3(esk1_2(k9_relat_1(esk7_0,esk6_0),k9_relat_1(esk8_0,esk6_0)),esk6_0,esk7_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])])).
% 0.14/0.38  cnf(c_0_20, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(esk1_2(k9_relat_1(esk7_0,esk6_0),k9_relat_1(esk8_0,esk6_0)),esk6_0,esk7_0),esk1_2(k9_relat_1(esk7_0,esk6_0),k9_relat_1(esk8_0,esk6_0))),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_13]), c_0_14])])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (r2_hidden(X1,k9_relat_1(X2,esk6_0))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(esk5_3(esk1_2(k9_relat_1(esk7_0,esk6_0),k9_relat_1(esk8_0,esk6_0)),esk6_0,esk7_0),X1),X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(esk1_2(k9_relat_1(esk7_0,esk6_0),k9_relat_1(esk8_0,esk6_0)),esk6_0,esk7_0),esk1_2(k9_relat_1(esk7_0,esk6_0),k9_relat_1(esk8_0,esk6_0))),esk8_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.38  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(esk1_2(k9_relat_1(esk7_0,esk6_0),k9_relat_1(esk8_0,esk6_0)),k9_relat_1(esk8_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_9]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 28
% 0.14/0.38  # Proof object clause steps            : 19
% 0.14/0.38  # Proof object formula steps           : 9
% 0.14/0.38  # Proof object conjectures             : 15
% 0.14/0.38  # Proof object clause conjectures      : 12
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 10
% 0.14/0.38  # Proof object initial formulas used   : 4
% 0.14/0.38  # Proof object generating inferences   : 8
% 0.14/0.38  # Proof object simplifying inferences  : 8
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 4
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 17
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 17
% 0.14/0.38  # Processed clauses                    : 45
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 1
% 0.14/0.38  # ...remaining for further processing  : 44
% 0.14/0.38  # Other redundant clauses eliminated   : 3
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 0
% 0.14/0.38  # Generated clauses                    : 36
% 0.14/0.38  # ...of the previous two non-trivial   : 34
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 33
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 3
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 25
% 0.14/0.38  #    Positive orientable unit clauses  : 10
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 1
% 0.14/0.38  #    Non-unit-clauses                  : 14
% 0.14/0.38  # Current number of unprocessed clauses: 15
% 0.14/0.38  # ...number of literals in the above   : 50
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 16
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 87
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 60
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.14/0.38  # Unit Clause-clause subsumption calls : 0
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 0
% 0.14/0.38  # BW rewrite match successes           : 0
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 2233
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.029 s
% 0.14/0.38  # System time              : 0.003 s
% 0.14/0.38  # Total time               : 0.032 s
% 0.14/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
