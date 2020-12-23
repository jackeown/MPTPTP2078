%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:03 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  68 expanded)
%              Number of clauses        :   22 (  28 expanded)
%              Number of leaves         :    4 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  119 ( 292 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t158_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ! [X4] :
          ( v1_relat_1(X4)
         => ( ( r1_tarski(X3,X4)
              & r1_tarski(X1,X2) )
           => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ! [X4] :
            ( v1_relat_1(X4)
           => ( ( r1_tarski(X3,X4)
                & r1_tarski(X1,X2) )
             => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t158_relat_1])).

fof(c_0_5,plain,(
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

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & v1_relat_1(esk9_0)
    & r1_tarski(esk8_0,esk9_0)
    & r1_tarski(esk6_0,esk7_0)
    & ~ r1_tarski(k9_relat_1(esk8_0,esk6_0),k9_relat_1(esk9_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X2,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X5 != k9_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
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

cnf(c_0_12,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk8_0,esk6_0),k9_relat_1(esk9_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,X1),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk1_2(k9_relat_1(esk8_0,esk6_0),k9_relat_1(esk9_0,esk7_0)),k9_relat_1(esk8_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(X1,k9_relat_1(X2,esk7_0))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X3,esk6_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk5_3(esk1_2(k9_relat_1(esk8_0,esk6_0),k9_relat_1(esk9_0,esk7_0)),esk6_0,esk8_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(esk1_2(k9_relat_1(esk8_0,esk6_0),k9_relat_1(esk9_0,esk7_0)),esk6_0,esk8_0),esk1_2(k9_relat_1(esk8_0,esk6_0),k9_relat_1(esk9_0,esk7_0))),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_17]),c_0_18])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,k9_relat_1(X2,esk7_0))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(esk5_3(esk1_2(k9_relat_1(esk8_0,esk6_0),k9_relat_1(esk9_0,esk7_0)),esk6_0,esk8_0),X1),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(esk1_2(k9_relat_1(esk8_0,esk6_0),k9_relat_1(esk9_0,esk7_0)),esk6_0,esk8_0),esk1_2(k9_relat_1(esk8_0,esk6_0),k9_relat_1(esk9_0,esk7_0))),esk9_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_2(k9_relat_1(esk8_0,esk6_0),k9_relat_1(esk9_0,esk7_0)),k9_relat_1(esk9_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_12]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n020.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:52:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.20/0.37  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.027 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t158_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_relat_1)).
% 0.20/0.37  fof(d13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X5,X4),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 0.20/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.37  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.20/0.37  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2)))))), inference(assume_negation,[status(cth)],[t158_relat_1])).
% 0.20/0.37  fof(c_0_5, plain, ![X12, X13, X14, X15, X17, X18, X19, X20, X22]:((((r2_hidden(k4_tarski(esk2_4(X12,X13,X14,X15),X15),X12)|~r2_hidden(X15,X14)|X14!=k9_relat_1(X12,X13)|~v1_relat_1(X12))&(r2_hidden(esk2_4(X12,X13,X14,X15),X13)|~r2_hidden(X15,X14)|X14!=k9_relat_1(X12,X13)|~v1_relat_1(X12)))&(~r2_hidden(k4_tarski(X18,X17),X12)|~r2_hidden(X18,X13)|r2_hidden(X17,X14)|X14!=k9_relat_1(X12,X13)|~v1_relat_1(X12)))&((~r2_hidden(esk3_3(X12,X19,X20),X20)|(~r2_hidden(k4_tarski(X22,esk3_3(X12,X19,X20)),X12)|~r2_hidden(X22,X19))|X20=k9_relat_1(X12,X19)|~v1_relat_1(X12))&((r2_hidden(k4_tarski(esk4_3(X12,X19,X20),esk3_3(X12,X19,X20)),X12)|r2_hidden(esk3_3(X12,X19,X20),X20)|X20=k9_relat_1(X12,X19)|~v1_relat_1(X12))&(r2_hidden(esk4_3(X12,X19,X20),X19)|r2_hidden(esk3_3(X12,X19,X20),X20)|X20=k9_relat_1(X12,X19)|~v1_relat_1(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).
% 0.20/0.37  fof(c_0_6, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.37  fof(c_0_7, negated_conjecture, (v1_relat_1(esk8_0)&(v1_relat_1(esk9_0)&((r1_tarski(esk8_0,esk9_0)&r1_tarski(esk6_0,esk7_0))&~r1_tarski(k9_relat_1(esk8_0,esk6_0),k9_relat_1(esk9_0,esk7_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.20/0.37  cnf(c_0_8, plain, (r2_hidden(X2,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X5!=k9_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.37  cnf(c_0_9, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  cnf(c_0_10, negated_conjecture, (r1_tarski(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  fof(c_0_11, plain, ![X24, X25, X26, X28]:((((r2_hidden(esk5_3(X24,X25,X26),k1_relat_1(X26))|~r2_hidden(X24,k9_relat_1(X26,X25))|~v1_relat_1(X26))&(r2_hidden(k4_tarski(esk5_3(X24,X25,X26),X24),X26)|~r2_hidden(X24,k9_relat_1(X26,X25))|~v1_relat_1(X26)))&(r2_hidden(esk5_3(X24,X25,X26),X25)|~r2_hidden(X24,k9_relat_1(X26,X25))|~v1_relat_1(X26)))&(~r2_hidden(X28,k1_relat_1(X26))|~r2_hidden(k4_tarski(X28,X24),X26)|~r2_hidden(X28,X25)|r2_hidden(X24,k9_relat_1(X26,X25))|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.20/0.37  cnf(c_0_12, negated_conjecture, (~r1_tarski(k9_relat_1(esk8_0,esk6_0),k9_relat_1(esk9_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_13, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  cnf(c_0_14, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X4,X1),X2)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_8])).
% 0.20/0.37  cnf(c_0_15, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.20/0.37  cnf(c_0_16, plain, (r2_hidden(esk5_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.37  cnf(c_0_17, negated_conjecture, (r2_hidden(esk1_2(k9_relat_1(esk8_0,esk6_0),k9_relat_1(esk9_0,esk7_0)),k9_relat_1(esk8_0,esk6_0))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.37  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_19, negated_conjecture, (r1_tarski(esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_20, plain, (r2_hidden(k4_tarski(esk5_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.37  cnf(c_0_21, negated_conjecture, (r2_hidden(X1,k9_relat_1(X2,esk7_0))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X3,esk6_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.37  cnf(c_0_22, negated_conjecture, (r2_hidden(esk5_3(esk1_2(k9_relat_1(esk8_0,esk6_0),k9_relat_1(esk9_0,esk7_0)),esk6_0,esk8_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 0.20/0.37  cnf(c_0_23, negated_conjecture, (r2_hidden(X1,esk9_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_9, c_0_19])).
% 0.20/0.37  cnf(c_0_24, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(esk1_2(k9_relat_1(esk8_0,esk6_0),k9_relat_1(esk9_0,esk7_0)),esk6_0,esk8_0),esk1_2(k9_relat_1(esk8_0,esk6_0),k9_relat_1(esk9_0,esk7_0))),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_17]), c_0_18])])).
% 0.20/0.37  cnf(c_0_25, negated_conjecture, (r2_hidden(X1,k9_relat_1(X2,esk7_0))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(esk5_3(esk1_2(k9_relat_1(esk8_0,esk6_0),k9_relat_1(esk9_0,esk7_0)),esk6_0,esk8_0),X1),X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.37  cnf(c_0_26, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(esk1_2(k9_relat_1(esk8_0,esk6_0),k9_relat_1(esk9_0,esk7_0)),esk6_0,esk8_0),esk1_2(k9_relat_1(esk8_0,esk6_0),k9_relat_1(esk9_0,esk7_0))),esk9_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.37  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  cnf(c_0_29, negated_conjecture, (r2_hidden(esk1_2(k9_relat_1(esk8_0,esk6_0),k9_relat_1(esk9_0,esk7_0)),k9_relat_1(esk9_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.20/0.37  cnf(c_0_30, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_12]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 31
% 0.20/0.37  # Proof object clause steps            : 22
% 0.20/0.37  # Proof object formula steps           : 9
% 0.20/0.37  # Proof object conjectures             : 18
% 0.20/0.37  # Proof object clause conjectures      : 15
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 11
% 0.20/0.37  # Proof object initial formulas used   : 4
% 0.20/0.37  # Proof object generating inferences   : 10
% 0.20/0.37  # Proof object simplifying inferences  : 8
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 4
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 18
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 18
% 0.20/0.37  # Processed clauses                    : 57
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 1
% 0.20/0.37  # ...remaining for further processing  : 56
% 0.20/0.37  # Other redundant clauses eliminated   : 3
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 0
% 0.20/0.37  # Generated clauses                    : 95
% 0.20/0.37  # ...of the previous two non-trivial   : 91
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 92
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 3
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 36
% 0.20/0.37  #    Positive orientable unit clauses  : 12
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 1
% 0.20/0.37  #    Non-unit-clauses                  : 23
% 0.20/0.37  # Current number of unprocessed clauses: 61
% 0.20/0.37  # ...number of literals in the above   : 203
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 17
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 180
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 130
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.37  # Unit Clause-clause subsumption calls : 0
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 0
% 0.20/0.37  # BW rewrite match successes           : 0
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 3345
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.028 s
% 0.20/0.37  # System time              : 0.007 s
% 0.20/0.37  # Total time               : 0.035 s
% 0.20/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
