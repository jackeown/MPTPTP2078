%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:56 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 127 expanded)
%              Number of clauses        :   31 (  62 expanded)
%              Number of leaves         :    3 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :  134 ( 657 expanded)
%              Number of equality atoms :   10 (  40 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t70_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
            & r1_xboole_0(X1,X2)
            & r1_xboole_0(X1,X3) )
        & ~ ( ~ ( r1_xboole_0(X1,X2)
                & r1_xboole_0(X1,X3) )
            & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t70_xboole_1])).

fof(c_0_4,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | r1_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_5,negated_conjecture,
    ( ( ~ r1_xboole_0(esk3_0,esk4_0)
      | ~ r1_xboole_0(esk3_0,esk5_0)
      | ~ r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0)) )
    & ( r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
      | ~ r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0)) )
    & ( ~ r1_xboole_0(esk3_0,esk4_0)
      | ~ r1_xboole_0(esk3_0,esk5_0)
      | r1_xboole_0(esk3_0,esk4_0) )
    & ( r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
      | r1_xboole_0(esk3_0,esk4_0) )
    & ( ~ r1_xboole_0(esk3_0,esk4_0)
      | ~ r1_xboole_0(esk3_0,esk5_0)
      | r1_xboole_0(esk3_0,esk5_0) )
    & ( r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
      | r1_xboole_0(esk3_0,esk5_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(X8,X5)
        | r2_hidden(X8,X6)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k2_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_7,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
    | r1_xboole_0(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
    | r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0)
    | r1_xboole_0(esk3_0,X1)
    | ~ r2_hidden(esk2_2(esk3_0,X1),k2_xboole_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0)
    | r1_xboole_0(esk3_0,X1)
    | ~ r2_hidden(esk2_2(esk3_0,X1),k2_xboole_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_11])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_21])).

cnf(c_0_26,plain,
    ( r1_xboole_0(k2_xboole_0(X1,X2),X3)
    | r2_hidden(esk2_2(k2_xboole_0(X1,X2),X3),X1)
    | r2_hidden(esk2_2(k2_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(X1,esk5_0),X2)
    | r2_hidden(esk2_2(k2_xboole_0(X1,esk5_0),X2),X1)
    | ~ r2_hidden(esk2_2(k2_xboole_0(X1,esk5_0),X2),esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(X1,esk5_0),esk3_0)
    | r2_hidden(esk2_2(k2_xboole_0(X1,esk5_0),esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk4_0,esk5_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,esk4_0)
    | ~ r1_xboole_0(esk3_0,esk5_0)
    | ~ r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(X1,k2_xboole_0(esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))
    | ~ r1_xboole_0(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_21])])).

cnf(c_0_35,negated_conjecture,
    ( r1_xboole_0(esk3_0,X1)
    | ~ r2_hidden(esk2_2(esk3_0,X1),k2_xboole_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_27])])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_13]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:34:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 3.62/3.79  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 3.62/3.79  # and selection function SelectNewComplexAHP.
% 3.62/3.79  #
% 3.62/3.79  # Preprocessing time       : 0.027 s
% 3.62/3.79  
% 3.62/3.79  # Proof found!
% 3.62/3.79  # SZS status Theorem
% 3.62/3.79  # SZS output start CNFRefutation
% 3.62/3.79  fof(t70_xboole_1, conjecture, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.62/3.79  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.62/3.79  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.62/3.79  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3)))))), inference(assume_negation,[status(cth)],[t70_xboole_1])).
% 3.62/3.79  fof(c_0_4, plain, ![X14, X15, X17, X18, X19]:(((r2_hidden(esk2_2(X14,X15),X14)|r1_xboole_0(X14,X15))&(r2_hidden(esk2_2(X14,X15),X15)|r1_xboole_0(X14,X15)))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|~r1_xboole_0(X17,X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 3.62/3.79  fof(c_0_5, negated_conjecture, ((((~r1_xboole_0(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,esk5_0)|~r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0)))&(r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))|~r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))))&((~r1_xboole_0(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,esk5_0)|r1_xboole_0(esk3_0,esk4_0))&(r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))|r1_xboole_0(esk3_0,esk4_0))))&((~r1_xboole_0(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,esk5_0)|r1_xboole_0(esk3_0,esk5_0))&(r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))|r1_xboole_0(esk3_0,esk5_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])).
% 3.62/3.79  fof(c_0_6, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(r2_hidden(X8,X5)|r2_hidden(X8,X6))|X7!=k2_xboole_0(X5,X6))&((~r2_hidden(X9,X5)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))&(~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))))&(((~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k2_xboole_0(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 3.62/3.79  cnf(c_0_7, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 3.62/3.79  cnf(c_0_8, negated_conjecture, (r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))|r1_xboole_0(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 3.62/3.79  cnf(c_0_9, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 3.62/3.79  cnf(c_0_10, negated_conjecture, (r1_xboole_0(esk3_0,esk5_0)|~r2_hidden(X1,k2_xboole_0(esk4_0,esk5_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 3.62/3.79  cnf(c_0_11, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 3.62/3.79  cnf(c_0_12, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_9])).
% 3.62/3.79  cnf(c_0_13, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 3.62/3.79  cnf(c_0_14, negated_conjecture, (r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))|r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 3.62/3.79  cnf(c_0_15, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 3.62/3.79  cnf(c_0_16, negated_conjecture, (r1_xboole_0(esk3_0,esk5_0)|r1_xboole_0(esk3_0,X1)|~r2_hidden(esk2_2(esk3_0,X1),k2_xboole_0(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 3.62/3.79  cnf(c_0_17, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 3.62/3.79  cnf(c_0_18, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 3.62/3.79  cnf(c_0_19, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)|~r2_hidden(X1,k2_xboole_0(esk4_0,esk5_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_7, c_0_14])).
% 3.62/3.79  cnf(c_0_20, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_15])).
% 3.62/3.79  cnf(c_0_21, negated_conjecture, (r1_xboole_0(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 3.62/3.79  cnf(c_0_22, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_18])).
% 3.62/3.79  cnf(c_0_23, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)|r1_xboole_0(esk3_0,X1)|~r2_hidden(esk2_2(esk3_0,X1),k2_xboole_0(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_19, c_0_11])).
% 3.62/3.79  cnf(c_0_24, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_20, c_0_13])).
% 3.62/3.79  cnf(c_0_25, negated_conjecture, (~r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_7, c_0_21])).
% 3.62/3.79  cnf(c_0_26, plain, (r1_xboole_0(k2_xboole_0(X1,X2),X3)|r2_hidden(esk2_2(k2_xboole_0(X1,X2),X3),X1)|r2_hidden(esk2_2(k2_xboole_0(X1,X2),X3),X2)), inference(spm,[status(thm)],[c_0_22, c_0_11])).
% 3.62/3.79  cnf(c_0_27, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 3.62/3.79  cnf(c_0_28, negated_conjecture, (r1_xboole_0(k2_xboole_0(X1,esk5_0),X2)|r2_hidden(esk2_2(k2_xboole_0(X1,esk5_0),X2),X1)|~r2_hidden(esk2_2(k2_xboole_0(X1,esk5_0),X2),esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 3.62/3.79  cnf(c_0_29, negated_conjecture, (~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_7, c_0_27])).
% 3.62/3.79  cnf(c_0_30, negated_conjecture, (r1_xboole_0(k2_xboole_0(X1,esk5_0),esk3_0)|r2_hidden(esk2_2(k2_xboole_0(X1,esk5_0),esk3_0),X1)), inference(spm,[status(thm)],[c_0_28, c_0_13])).
% 3.62/3.79  cnf(c_0_31, negated_conjecture, (r1_xboole_0(k2_xboole_0(esk4_0,esk5_0),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_13])).
% 3.62/3.79  cnf(c_0_32, negated_conjecture, (~r1_xboole_0(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,esk5_0)|~r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 3.62/3.79  cnf(c_0_33, negated_conjecture, (~r2_hidden(X1,k2_xboole_0(esk4_0,esk5_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_7, c_0_31])).
% 3.62/3.79  cnf(c_0_34, negated_conjecture, (~r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))|~r1_xboole_0(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_21])])).
% 3.62/3.79  cnf(c_0_35, negated_conjecture, (r1_xboole_0(esk3_0,X1)|~r2_hidden(esk2_2(esk3_0,X1),k2_xboole_0(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_33, c_0_11])).
% 3.62/3.79  cnf(c_0_36, negated_conjecture, (~r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_27])])).
% 3.62/3.79  cnf(c_0_37, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_13]), c_0_36]), ['proof']).
% 3.62/3.79  # SZS output end CNFRefutation
% 3.62/3.79  # Proof object total steps             : 38
% 3.62/3.79  # Proof object clause steps            : 31
% 3.62/3.79  # Proof object formula steps           : 7
% 3.62/3.79  # Proof object conjectures             : 22
% 3.62/3.79  # Proof object clause conjectures      : 19
% 3.62/3.79  # Proof object formula conjectures     : 3
% 3.62/3.79  # Proof object initial clauses used    : 9
% 3.62/3.79  # Proof object initial formulas used   : 3
% 3.62/3.79  # Proof object generating inferences   : 20
% 3.62/3.79  # Proof object simplifying inferences  : 6
% 3.62/3.79  # Training examples: 0 positive, 0 negative
% 3.62/3.79  # Parsed axioms                        : 3
% 3.62/3.79  # Removed by relevancy pruning/SinE    : 0
% 3.62/3.79  # Initial clauses                      : 15
% 3.62/3.79  # Removed in clause preprocessing      : 3
% 3.62/3.79  # Initial clauses in saturation        : 12
% 3.62/3.79  # Processed clauses                    : 15206
% 3.62/3.79  # ...of these trivial                  : 2547
% 3.62/3.79  # ...subsumed                          : 11942
% 3.62/3.79  # ...remaining for further processing  : 717
% 3.62/3.79  # Other redundant clauses eliminated   : 3
% 3.62/3.79  # Clauses deleted for lack of memory   : 0
% 3.62/3.79  # Backward-subsumed                    : 2
% 3.62/3.79  # Backward-rewritten                   : 14
% 3.62/3.79  # Generated clauses                    : 598280
% 3.62/3.79  # ...of the previous two non-trivial   : 440764
% 3.62/3.79  # Contextual simplify-reflections      : 9
% 3.62/3.79  # Paramodulations                      : 597680
% 3.62/3.79  # Factorizations                       : 534
% 3.62/3.79  # Equation resolutions                 : 66
% 3.62/3.79  # Propositional unsat checks           : 0
% 3.62/3.79  #    Propositional check models        : 0
% 3.62/3.79  #    Propositional check unsatisfiable : 0
% 3.62/3.79  #    Propositional clauses             : 0
% 3.62/3.79  #    Propositional clauses after purity: 0
% 3.62/3.79  #    Propositional unsat core size     : 0
% 3.62/3.79  #    Propositional preprocessing time  : 0.000
% 3.62/3.79  #    Propositional encoding time       : 0.000
% 3.62/3.79  #    Propositional solver time         : 0.000
% 3.62/3.79  #    Success case prop preproc time    : 0.000
% 3.62/3.79  #    Success case prop encoding time   : 0.000
% 3.62/3.79  #    Success case prop solver time     : 0.000
% 3.62/3.79  # Current number of processed clauses  : 701
% 3.62/3.79  #    Positive orientable unit clauses  : 252
% 3.62/3.79  #    Positive unorientable unit clauses: 0
% 3.62/3.79  #    Negative unit clauses             : 1
% 3.62/3.79  #    Non-unit-clauses                  : 448
% 3.62/3.79  # Current number of unprocessed clauses: 425521
% 3.62/3.79  # ...number of literals in the above   : 869643
% 3.62/3.79  # Current number of archived formulas  : 0
% 3.62/3.79  # Current number of archived clauses   : 16
% 3.62/3.79  # Clause-clause subsumption calls (NU) : 403820
% 3.62/3.79  # Rec. Clause-clause subsumption calls : 382688
% 3.62/3.79  # Non-unit clause-clause subsumptions  : 11953
% 3.62/3.79  # Unit Clause-clause subsumption calls : 11
% 3.62/3.79  # Rewrite failures with RHS unbound    : 0
% 3.62/3.79  # BW rewrite match attempts            : 17253
% 3.62/3.79  # BW rewrite match successes           : 4
% 3.62/3.79  # Condensation attempts                : 0
% 3.62/3.79  # Condensation successes               : 0
% 3.62/3.79  # Termbank termtop insertions          : 9520872
% 3.62/3.80  
% 3.62/3.80  # -------------------------------------------------
% 3.62/3.80  # User time                : 3.307 s
% 3.62/3.80  # System time              : 0.161 s
% 3.62/3.80  # Total time               : 3.469 s
% 3.62/3.80  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
