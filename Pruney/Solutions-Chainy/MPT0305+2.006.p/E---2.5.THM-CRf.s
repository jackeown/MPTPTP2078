%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:36 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   32 (  84 expanded)
%              Number of clauses        :   23 (  37 expanded)
%              Number of leaves         :    4 (  20 expanded)
%              Depth                    :   12
%              Number of atoms          :   75 ( 259 expanded)
%              Number of equality atoms :    7 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t117_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( X1 != k1_xboole_0
          & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
            | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
          & ~ r1_tarski(X2,X3) ) ),
    inference(assume_negation,[status(cth)],[t117_zfmisc_1])).

fof(c_0_5,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    & ( r1_tarski(k2_zfmisc_1(esk4_0,esk3_0),k2_zfmisc_1(esk5_0,esk3_0))
      | r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk5_0)) )
    & ~ r1_tarski(esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).

fof(c_0_6,plain,(
    ! [X11] :
      ( X11 = k1_xboole_0
      | r2_hidden(esk2_1(X11),X11) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_8,plain,(
    ! [X13,X14,X15,X16] :
      ( ( r2_hidden(X13,X15)
        | ~ r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)) )
      & ( r2_hidden(X14,X16)
        | ~ r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)) )
      & ( ~ r2_hidden(X13,X15)
        | ~ r2_hidden(X14,X16)
        | r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_9,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk2_1(esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_1(esk3_0)),k2_zfmisc_1(X2,esk3_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk1_2(esk4_0,esk5_0)),k2_zfmisc_1(X2,esk4_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_15])).

cnf(c_0_18,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk4_0,esk5_0),esk2_1(esk3_0)),k2_zfmisc_1(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_1(esk3_0),esk1_2(esk4_0,esk5_0)),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk4_0,esk5_0),esk2_1(esk3_0)),X1)
    | ~ r1_tarski(k2_zfmisc_1(esk4_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk4_0,esk3_0),k2_zfmisc_1(esk5_0,esk3_0))
    | r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_1(esk3_0),esk1_2(esk4_0,esk5_0)),X1)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk4_0,esk5_0),esk2_1(esk3_0)),k2_zfmisc_1(esk5_0,esk3_0))
    | r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk4_0,esk5_0),esk2_1(esk3_0)),k2_zfmisc_1(esk5_0,esk3_0))
    | r2_hidden(k4_tarski(esk2_1(esk3_0),esk1_2(esk4_0,esk5_0)),k2_zfmisc_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk4_0,esk5_0),esk2_1(esk3_0)),k2_zfmisc_1(esk5_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_16])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_11]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:24:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.78/0.99  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.78/0.99  # and selection function SelectSmallestOrientable.
% 0.78/0.99  #
% 0.78/0.99  # Preprocessing time       : 0.026 s
% 0.78/0.99  # Presaturation interreduction done
% 0.78/0.99  
% 0.78/0.99  # Proof found!
% 0.78/0.99  # SZS status Theorem
% 0.78/0.99  # SZS output start CNFRefutation
% 0.78/0.99  fof(t117_zfmisc_1, conjecture, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 0.78/0.99  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.78/0.99  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.78/0.99  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.78/0.99  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3))))), inference(assume_negation,[status(cth)],[t117_zfmisc_1])).
% 0.78/0.99  fof(c_0_5, negated_conjecture, ((esk3_0!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(esk4_0,esk3_0),k2_zfmisc_1(esk5_0,esk3_0))|r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk5_0))))&~r1_tarski(esk4_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).
% 0.78/0.99  fof(c_0_6, plain, ![X11]:(X11=k1_xboole_0|r2_hidden(esk2_1(X11),X11)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.78/0.99  fof(c_0_7, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.78/0.99  fof(c_0_8, plain, ![X13, X14, X15, X16]:(((r2_hidden(X13,X15)|~r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)))&(r2_hidden(X14,X16)|~r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16))))&(~r2_hidden(X13,X15)|~r2_hidden(X14,X16)|r2_hidden(k4_tarski(X13,X14),k2_zfmisc_1(X15,X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.78/0.99  cnf(c_0_9, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.78/0.99  cnf(c_0_10, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.78/0.99  cnf(c_0_11, negated_conjecture, (~r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.78/0.99  cnf(c_0_12, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.78/0.99  cnf(c_0_13, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.78/0.99  cnf(c_0_14, negated_conjecture, (r2_hidden(esk2_1(esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.78/0.99  cnf(c_0_15, negated_conjecture, (r2_hidden(esk1_2(esk4_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.78/0.99  cnf(c_0_16, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_1(esk3_0)),k2_zfmisc_1(X2,esk3_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.78/0.99  cnf(c_0_17, negated_conjecture, (r2_hidden(k4_tarski(X1,esk1_2(esk4_0,esk5_0)),k2_zfmisc_1(X2,esk4_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_13, c_0_15])).
% 0.78/0.99  cnf(c_0_18, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.78/0.99  cnf(c_0_19, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk4_0,esk5_0),esk2_1(esk3_0)),k2_zfmisc_1(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_16, c_0_15])).
% 0.78/0.99  cnf(c_0_20, negated_conjecture, (r2_hidden(k4_tarski(esk2_1(esk3_0),esk1_2(esk4_0,esk5_0)),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_17, c_0_14])).
% 0.78/0.99  cnf(c_0_21, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk4_0,esk5_0),esk2_1(esk3_0)),X1)|~r1_tarski(k2_zfmisc_1(esk4_0,esk3_0),X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.78/0.99  cnf(c_0_22, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk4_0,esk3_0),k2_zfmisc_1(esk5_0,esk3_0))|r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.78/0.99  cnf(c_0_23, negated_conjecture, (r2_hidden(k4_tarski(esk2_1(esk3_0),esk1_2(esk4_0,esk5_0)),X1)|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_18, c_0_20])).
% 0.78/0.99  cnf(c_0_24, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk4_0,esk5_0),esk2_1(esk3_0)),k2_zfmisc_1(esk5_0,esk3_0))|r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.78/0.99  cnf(c_0_25, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.78/0.99  cnf(c_0_26, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk4_0,esk5_0),esk2_1(esk3_0)),k2_zfmisc_1(esk5_0,esk3_0))|r2_hidden(k4_tarski(esk2_1(esk3_0),esk1_2(esk4_0,esk5_0)),k2_zfmisc_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.78/0.99  cnf(c_0_27, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.78/0.99  cnf(c_0_28, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk4_0,esk5_0),esk2_1(esk3_0)),k2_zfmisc_1(esk5_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_16])).
% 0.78/0.99  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.78/0.99  cnf(c_0_30, negated_conjecture, (r2_hidden(esk1_2(esk4_0,esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.78/0.99  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_11]), ['proof']).
% 0.78/0.99  # SZS output end CNFRefutation
% 0.78/0.99  # Proof object total steps             : 32
% 0.78/0.99  # Proof object clause steps            : 23
% 0.78/0.99  # Proof object formula steps           : 9
% 0.78/0.99  # Proof object conjectures             : 19
% 0.78/0.99  # Proof object clause conjectures      : 16
% 0.78/0.99  # Proof object formula conjectures     : 3
% 0.78/0.99  # Proof object initial clauses used    : 10
% 0.78/0.99  # Proof object initial formulas used   : 4
% 0.78/0.99  # Proof object generating inferences   : 13
% 0.78/0.99  # Proof object simplifying inferences  : 2
% 0.78/0.99  # Training examples: 0 positive, 0 negative
% 0.78/0.99  # Parsed axioms                        : 4
% 0.78/0.99  # Removed by relevancy pruning/SinE    : 0
% 0.78/0.99  # Initial clauses                      : 10
% 0.78/0.99  # Removed in clause preprocessing      : 0
% 0.78/0.99  # Initial clauses in saturation        : 10
% 0.78/0.99  # Processed clauses                    : 1631
% 0.78/0.99  # ...of these trivial                  : 1
% 0.78/0.99  # ...subsumed                          : 689
% 0.78/0.99  # ...remaining for further processing  : 941
% 0.78/0.99  # Other redundant clauses eliminated   : 0
% 0.78/0.99  # Clauses deleted for lack of memory   : 0
% 0.78/0.99  # Backward-subsumed                    : 7
% 0.78/0.99  # Backward-rewritten                   : 6
% 0.78/0.99  # Generated clauses                    : 66735
% 0.78/0.99  # ...of the previous two non-trivial   : 63787
% 0.78/0.99  # Contextual simplify-reflections      : 5
% 0.78/0.99  # Paramodulations                      : 66703
% 0.78/0.99  # Factorizations                       : 32
% 0.78/0.99  # Equation resolutions                 : 0
% 0.78/0.99  # Propositional unsat checks           : 0
% 0.78/0.99  #    Propositional check models        : 0
% 0.78/0.99  #    Propositional check unsatisfiable : 0
% 0.78/0.99  #    Propositional clauses             : 0
% 0.78/0.99  #    Propositional clauses after purity: 0
% 0.78/0.99  #    Propositional unsat core size     : 0
% 0.78/0.99  #    Propositional preprocessing time  : 0.000
% 0.78/0.99  #    Propositional encoding time       : 0.000
% 0.78/0.99  #    Propositional solver time         : 0.000
% 0.78/0.99  #    Success case prop preproc time    : 0.000
% 0.78/0.99  #    Success case prop encoding time   : 0.000
% 0.78/0.99  #    Success case prop solver time     : 0.000
% 0.78/0.99  # Current number of processed clauses  : 918
% 0.78/0.99  #    Positive orientable unit clauses  : 24
% 0.78/0.99  #    Positive unorientable unit clauses: 0
% 0.78/0.99  #    Negative unit clauses             : 2
% 0.78/0.99  #    Non-unit-clauses                  : 892
% 0.78/0.99  # Current number of unprocessed clauses: 62048
% 0.78/0.99  # ...number of literals in the above   : 297157
% 0.78/0.99  # Current number of archived formulas  : 0
% 0.78/0.99  # Current number of archived clauses   : 23
% 0.78/0.99  # Clause-clause subsumption calls (NU) : 55689
% 0.78/0.99  # Rec. Clause-clause subsumption calls : 9487
% 0.78/0.99  # Non-unit clause-clause subsumptions  : 701
% 0.78/0.99  # Unit Clause-clause subsumption calls : 536
% 0.78/0.99  # Rewrite failures with RHS unbound    : 0
% 0.78/0.99  # BW rewrite match attempts            : 29
% 0.78/0.99  # BW rewrite match successes           : 1
% 0.78/0.99  # Condensation attempts                : 0
% 0.78/0.99  # Condensation successes               : 0
% 0.78/0.99  # Termbank termtop insertions          : 1638807
% 0.78/0.99  
% 0.78/0.99  # -------------------------------------------------
% 0.78/0.99  # User time                : 0.619 s
% 0.78/0.99  # System time              : 0.035 s
% 0.78/0.99  # Total time               : 0.655 s
% 0.78/0.99  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
