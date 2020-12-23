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
% DateTime   : Thu Dec  3 10:51:03 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   34 (  95 expanded)
%              Number of clauses        :   25 (  37 expanded)
%              Number of leaves         :    4 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :   99 ( 387 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
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

fof(t157_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ! [X4] :
            ( v1_relat_1(X4)
           => ( ( r1_tarski(X3,X4)
                & r1_tarski(X1,X2) )
             => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t158_relat_1])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_relat_1(esk6_0)
    & r1_tarski(esk5_0,esk6_0)
    & r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

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

fof(c_0_7,plain,(
    ! [X11,X12,X13,X15] :
      ( ( r2_hidden(esk2_3(X11,X12,X13),k1_relat_1(X13))
        | ~ r2_hidden(X11,k9_relat_1(X13,X12))
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk2_3(X11,X12,X13),X11),X13)
        | ~ r2_hidden(X11,k9_relat_1(X13,X12))
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(esk2_3(X11,X12,X13),X12)
        | ~ r2_hidden(X11,k9_relat_1(X13,X12))
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(X15,k1_relat_1(X13))
        | ~ r2_hidden(k4_tarski(X15,X11),X13)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X11,k9_relat_1(X13,X12))
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_8,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),k9_relat_1(esk5_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk2_3(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),esk3_0,esk5_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,k9_relat_1(X2,X4))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_3(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),esk3_0,esk5_0),esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0))),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_11]),c_0_12])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk2_3(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),esk3_0,esk5_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_11]),c_0_12])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk2_3(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),esk3_0,esk5_0),X1)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),k9_relat_1(esk5_0,X1))
    | ~ r2_hidden(esk2_3(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),esk3_0,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_12]),c_0_19])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk2_3(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),esk3_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),k9_relat_1(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_25,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X17)
      | ~ v1_relat_1(X18)
      | ~ r1_tarski(X17,X18)
      | r1_tarski(k9_relat_1(X17,X16),k9_relat_1(X18,X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_relat_1])])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),X1)
    | ~ r1_tarski(k9_relat_1(esk5_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_24])).

cnf(c_0_27,plain,
    ( r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),k9_relat_1(X1,esk4_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_12])])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),k9_relat_1(esk6_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_8]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:08:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S02CA
% 0.19/0.38  # and selection function SelectAntiRROptimalLit.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.039 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t158_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_relat_1)).
% 0.19/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.38  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.19/0.38  fof(t157_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_relat_1)).
% 0.19/0.38  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2)))))), inference(assume_negation,[status(cth)],[t158_relat_1])).
% 0.19/0.38  fof(c_0_5, negated_conjecture, (v1_relat_1(esk5_0)&(v1_relat_1(esk6_0)&((r1_tarski(esk5_0,esk6_0)&r1_tarski(esk3_0,esk4_0))&~r1_tarski(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.19/0.38  fof(c_0_6, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.38  fof(c_0_7, plain, ![X11, X12, X13, X15]:((((r2_hidden(esk2_3(X11,X12,X13),k1_relat_1(X13))|~r2_hidden(X11,k9_relat_1(X13,X12))|~v1_relat_1(X13))&(r2_hidden(k4_tarski(esk2_3(X11,X12,X13),X11),X13)|~r2_hidden(X11,k9_relat_1(X13,X12))|~v1_relat_1(X13)))&(r2_hidden(esk2_3(X11,X12,X13),X12)|~r2_hidden(X11,k9_relat_1(X13,X12))|~v1_relat_1(X13)))&(~r2_hidden(X15,k1_relat_1(X13))|~r2_hidden(k4_tarski(X15,X11),X13)|~r2_hidden(X15,X12)|r2_hidden(X11,k9_relat_1(X13,X12))|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.19/0.38  cnf(c_0_8, negated_conjecture, (~r1_tarski(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.38  cnf(c_0_9, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_10, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  cnf(c_0_11, negated_conjecture, (r2_hidden(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),k9_relat_1(esk5_0,esk3_0))), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.19/0.38  cnf(c_0_12, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.38  cnf(c_0_13, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  cnf(c_0_14, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  cnf(c_0_15, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_16, negated_conjecture, (r2_hidden(esk2_3(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),esk3_0,esk5_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])])).
% 0.19/0.38  cnf(c_0_17, plain, (r2_hidden(X3,k9_relat_1(X2,X4))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (r2_hidden(k4_tarski(esk2_3(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),esk3_0,esk5_0),esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0))),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_11]), c_0_12])])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (r2_hidden(esk2_3(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),esk3_0,esk5_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_11]), c_0_12])])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (r2_hidden(esk2_3(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),esk3_0,esk5_0),X1)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (r2_hidden(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),k9_relat_1(esk5_0,X1))|~r2_hidden(esk2_3(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),esk3_0,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_12]), c_0_19])])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (r2_hidden(esk2_3(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),esk3_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),k9_relat_1(esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.38  fof(c_0_25, plain, ![X16, X17, X18]:(~v1_relat_1(X17)|(~v1_relat_1(X18)|(~r1_tarski(X17,X18)|r1_tarski(k9_relat_1(X17,X16),k9_relat_1(X18,X16))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_relat_1])])])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),X1)|~r1_tarski(k9_relat_1(esk5_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_15, c_0_24])).
% 0.19/0.38  cnf(c_0_27, plain, (r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),k9_relat_1(X1,esk4_0))|~v1_relat_1(X1)|~r1_tarski(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_12])])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.38  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (r2_hidden(esk1_2(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)),k9_relat_1(esk6_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_8]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 34
% 0.19/0.38  # Proof object clause steps            : 25
% 0.19/0.38  # Proof object formula steps           : 9
% 0.19/0.38  # Proof object conjectures             : 20
% 0.19/0.38  # Proof object clause conjectures      : 17
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 13
% 0.19/0.38  # Proof object initial formulas used   : 4
% 0.19/0.38  # Proof object generating inferences   : 12
% 0.19/0.38  # Proof object simplifying inferences  : 14
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 4
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 13
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 13
% 0.19/0.38  # Processed clauses                    : 69
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 0
% 0.19/0.38  # ...remaining for further processing  : 69
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 0
% 0.19/0.38  # Generated clauses                    : 104
% 0.19/0.38  # ...of the previous two non-trivial   : 94
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 104
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 56
% 0.19/0.38  #    Positive orientable unit clauses  : 15
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 40
% 0.19/0.38  # Current number of unprocessed clauses: 47
% 0.19/0.38  # ...number of literals in the above   : 123
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 13
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 157
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 140
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.38  # Unit Clause-clause subsumption calls : 15
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 2
% 0.19/0.38  # BW rewrite match successes           : 0
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 3601
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.042 s
% 0.19/0.38  # System time              : 0.005 s
% 0.19/0.38  # Total time               : 0.047 s
% 0.19/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
