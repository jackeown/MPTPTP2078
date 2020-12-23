%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:44 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   25 (  61 expanded)
%              Number of clauses        :   16 (  21 expanded)
%              Number of leaves         :    4 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   98 ( 306 expanded)
%              Number of equality atoms :   10 (  41 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ~ ( v2_wellord1(X1)
          & k3_relat_1(X1) != k1_xboole_0
          & ! [X2] :
              ~ ( r2_hidden(X2,k3_relat_1(X1))
                & ! [X3] :
                    ( r2_hidden(X3,k3_relat_1(X1))
                   => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord1)).

fof(t10_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => ! [X2] :
            ~ ( r1_tarski(X2,k3_relat_1(X1))
              & X2 != k1_xboole_0
              & ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( r2_hidden(X4,X2)
                       => r2_hidden(k4_tarski(X3,X4),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord1)).

fof(t31_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ~ ( v2_wellord1(X1)
            & k3_relat_1(X1) != k1_xboole_0
            & ! [X2] :
                ~ ( r2_hidden(X2,k3_relat_1(X1))
                  & ! [X3] :
                      ( r2_hidden(X3,k3_relat_1(X1))
                     => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t11_wellord1])).

fof(c_0_5,negated_conjecture,(
    ! [X19] :
      ( v1_relat_1(esk4_0)
      & v2_wellord1(esk4_0)
      & k3_relat_1(esk4_0) != k1_xboole_0
      & ( r2_hidden(esk5_1(X19),k3_relat_1(esk4_0))
        | ~ r2_hidden(X19,k3_relat_1(esk4_0)) )
      & ( ~ r2_hidden(k4_tarski(X19,esk5_1(X19)),esk4_0)
        | ~ r2_hidden(X19,k3_relat_1(esk4_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])])).

fof(c_0_6,plain,(
    ! [X14,X15,X17] :
      ( ( r2_hidden(esk3_2(X14,X15),X15)
        | ~ r1_tarski(X15,k3_relat_1(X14))
        | X15 = k1_xboole_0
        | ~ v2_wellord1(X14)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(X17,X15)
        | r2_hidden(k4_tarski(esk3_2(X14,X15),X17),X14)
        | ~ r1_tarski(X15,k3_relat_1(X14))
        | X15 = k1_xboole_0
        | ~ v2_wellord1(X14)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord1])])])])])).

cnf(c_0_7,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk5_1(X1)),esk4_0)
    | ~ r2_hidden(X1,k3_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(esk3_2(X3,X2),X1),X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,k3_relat_1(X3))
    | ~ v2_wellord1(X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( v2_wellord1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(esk3_2(esk4_0,X1),k3_relat_1(esk4_0))
    | ~ r2_hidden(esk5_1(esk3_2(esk4_0,X1)),X1)
    | ~ r1_tarski(X1,k3_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10])])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk5_1(X1),k3_relat_1(esk4_0))
    | ~ r2_hidden(X1,k3_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( k3_relat_1(esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( ~ r2_hidden(esk3_2(esk4_0,k3_relat_1(esk4_0)),k3_relat_1(esk4_0))
    | ~ r1_tarski(k3_relat_1(esk4_0),k3_relat_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

cnf(c_0_15,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k1_xboole_0
    | ~ r1_tarski(X2,k3_relat_1(X1))
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_16,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X12)
      | ~ v1_relat_1(X13)
      | ~ r1_tarski(X12,X13)
      | r1_tarski(k3_relat_1(X12),k3_relat_1(X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).

fof(c_0_17,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(k4_tarski(X7,X8),X5)
        | r2_hidden(k4_tarski(X7,X8),X6)
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(k4_tarski(esk1_2(X5,X9),esk2_2(X5,X9)),X5)
        | r1_tarski(X5,X9)
        | ~ v1_relat_1(X5) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X5,X9),esk2_2(X5,X9)),X9)
        | r1_tarski(X5,X9)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk4_0),k3_relat_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_9]),c_0_10])]),c_0_13])).

cnf(c_0_19,plain,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_10])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_10])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.13/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t11_wellord1, conjecture, ![X1]:(v1_relat_1(X1)=>~(((v2_wellord1(X1)&k3_relat_1(X1)!=k1_xboole_0)&![X2]:~((r2_hidden(X2,k3_relat_1(X1))&![X3]:(r2_hidden(X3,k3_relat_1(X1))=>r2_hidden(k4_tarski(X2,X3),X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord1)).
% 0.13/0.37  fof(t10_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)=>![X2]:~(((r1_tarski(X2,k3_relat_1(X1))&X2!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X2)&![X4]:(r2_hidden(X4,X2)=>r2_hidden(k4_tarski(X3,X4),X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord1)).
% 0.13/0.37  fof(t31_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 0.13/0.37  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 0.13/0.37  fof(c_0_4, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>~(((v2_wellord1(X1)&k3_relat_1(X1)!=k1_xboole_0)&![X2]:~((r2_hidden(X2,k3_relat_1(X1))&![X3]:(r2_hidden(X3,k3_relat_1(X1))=>r2_hidden(k4_tarski(X2,X3),X1)))))))), inference(assume_negation,[status(cth)],[t11_wellord1])).
% 0.13/0.37  fof(c_0_5, negated_conjecture, ![X19]:(v1_relat_1(esk4_0)&((v2_wellord1(esk4_0)&k3_relat_1(esk4_0)!=k1_xboole_0)&((r2_hidden(esk5_1(X19),k3_relat_1(esk4_0))|~r2_hidden(X19,k3_relat_1(esk4_0)))&(~r2_hidden(k4_tarski(X19,esk5_1(X19)),esk4_0)|~r2_hidden(X19,k3_relat_1(esk4_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])])).
% 0.13/0.37  fof(c_0_6, plain, ![X14, X15, X17]:((r2_hidden(esk3_2(X14,X15),X15)|(~r1_tarski(X15,k3_relat_1(X14))|X15=k1_xboole_0)|~v2_wellord1(X14)|~v1_relat_1(X14))&(~r2_hidden(X17,X15)|r2_hidden(k4_tarski(esk3_2(X14,X15),X17),X14)|(~r1_tarski(X15,k3_relat_1(X14))|X15=k1_xboole_0)|~v2_wellord1(X14)|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_wellord1])])])])])).
% 0.13/0.37  cnf(c_0_7, negated_conjecture, (~r2_hidden(k4_tarski(X1,esk5_1(X1)),esk4_0)|~r2_hidden(X1,k3_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_8, plain, (r2_hidden(k4_tarski(esk3_2(X3,X2),X1),X3)|X2=k1_xboole_0|~r2_hidden(X1,X2)|~r1_tarski(X2,k3_relat_1(X3))|~v2_wellord1(X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_9, negated_conjecture, (v2_wellord1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_10, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_11, negated_conjecture, (X1=k1_xboole_0|~r2_hidden(esk3_2(esk4_0,X1),k3_relat_1(esk4_0))|~r2_hidden(esk5_1(esk3_2(esk4_0,X1)),X1)|~r1_tarski(X1,k3_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9]), c_0_10])])).
% 0.13/0.37  cnf(c_0_12, negated_conjecture, (r2_hidden(esk5_1(X1),k3_relat_1(esk4_0))|~r2_hidden(X1,k3_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_13, negated_conjecture, (k3_relat_1(esk4_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_14, negated_conjecture, (~r2_hidden(esk3_2(esk4_0,k3_relat_1(esk4_0)),k3_relat_1(esk4_0))|~r1_tarski(k3_relat_1(esk4_0),k3_relat_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])).
% 0.13/0.37  cnf(c_0_15, plain, (r2_hidden(esk3_2(X1,X2),X2)|X2=k1_xboole_0|~r1_tarski(X2,k3_relat_1(X1))|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  fof(c_0_16, plain, ![X12, X13]:(~v1_relat_1(X12)|(~v1_relat_1(X13)|(~r1_tarski(X12,X13)|r1_tarski(k3_relat_1(X12),k3_relat_1(X13))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).
% 0.13/0.37  fof(c_0_17, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(k4_tarski(X7,X8),X5)|r2_hidden(k4_tarski(X7,X8),X6))|~v1_relat_1(X5))&((r2_hidden(k4_tarski(esk1_2(X5,X9),esk2_2(X5,X9)),X5)|r1_tarski(X5,X9)|~v1_relat_1(X5))&(~r2_hidden(k4_tarski(esk1_2(X5,X9),esk2_2(X5,X9)),X9)|r1_tarski(X5,X9)|~v1_relat_1(X5)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (~r1_tarski(k3_relat_1(esk4_0),k3_relat_1(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_9]), c_0_10])]), c_0_13])).
% 0.13/0.37  cnf(c_0_19, plain, (r1_tarski(k3_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_20, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  cnf(c_0_21, plain, (r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (~r1_tarski(esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_10])])).
% 0.13/0.37  cnf(c_0_23, plain, (r1_tarski(X1,X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_10])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 25
% 0.13/0.37  # Proof object clause steps            : 16
% 0.13/0.37  # Proof object formula steps           : 9
% 0.13/0.37  # Proof object conjectures             : 13
% 0.13/0.37  # Proof object clause conjectures      : 10
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 10
% 0.13/0.37  # Proof object initial formulas used   : 4
% 0.13/0.37  # Proof object generating inferences   : 6
% 0.13/0.37  # Proof object simplifying inferences  : 12
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 4
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 11
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 11
% 0.13/0.37  # Processed clauses                    : 20
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 20
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 15
% 0.13/0.37  # ...of the previous two non-trivial   : 13
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 15
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 20
% 0.13/0.37  #    Positive orientable unit clauses  : 2
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 4
% 0.13/0.37  #    Non-unit-clauses                  : 14
% 0.13/0.37  # Current number of unprocessed clauses: 4
% 0.13/0.37  # ...number of literals in the above   : 27
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 0
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 60
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 26
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 6
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 0
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1301
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.027 s
% 0.13/0.37  # System time              : 0.005 s
% 0.13/0.37  # Total time               : 0.032 s
% 0.13/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
