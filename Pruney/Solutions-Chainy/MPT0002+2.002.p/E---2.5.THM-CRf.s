%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:43 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 338 expanded)
%              Number of clauses        :   27 ( 144 expanded)
%              Number of leaves         :    3 (  76 expanded)
%              Depth                    :   14
%              Number of atoms          :  121 (1688 expanded)
%              Number of equality atoms :   17 ( 264 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_xboole_0,conjecture,(
    ! [X1,X2,X3] :
      ( ! [X4] :
          ( ~ r2_hidden(X4,X1)
        <=> ( r2_hidden(X4,X2)
          <=> r2_hidden(X4,X3) ) )
     => X1 = k5_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_0)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ! [X4] :
            ( ~ r2_hidden(X4,X1)
          <=> ( r2_hidden(X4,X2)
            <=> r2_hidden(X4,X3) ) )
       => X1 = k5_xboole_0(X2,X3) ) ),
    inference(assume_negation,[status(cth)],[t2_xboole_0])).

fof(c_0_4,negated_conjecture,(
    ! [X14] :
      ( ( ~ r2_hidden(X14,esk3_0)
        | r2_hidden(X14,esk4_0)
        | r2_hidden(X14,esk2_0) )
      & ( ~ r2_hidden(X14,esk4_0)
        | r2_hidden(X14,esk3_0)
        | r2_hidden(X14,esk2_0) )
      & ( ~ r2_hidden(X14,esk3_0)
        | ~ r2_hidden(X14,esk4_0)
        | ~ r2_hidden(X14,esk2_0) )
      & ( r2_hidden(X14,esk3_0)
        | r2_hidden(X14,esk4_0)
        | ~ r2_hidden(X14,esk2_0) )
      & esk2_0 != k5_xboole_0(esk3_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])])).

fof(c_0_5,plain,(
    ! [X8,X9] :
      ( ( ~ r2_hidden(esk1_2(X8,X9),X8)
        | ~ r2_hidden(esk1_2(X8,X9),X9)
        | X8 = X9 )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r2_hidden(esk1_2(X8,X9),X9)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

fof(c_0_6,plain,(
    ! [X5,X6,X7] :
      ( ( ~ r2_hidden(X5,X6)
        | ~ r2_hidden(X5,X7)
        | ~ r2_hidden(X5,k5_xboole_0(X6,X7)) )
      & ( r2_hidden(X5,X6)
        | r2_hidden(X5,X7)
        | ~ r2_hidden(X5,k5_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X5,X6)
        | r2_hidden(X5,X7)
        | r2_hidden(X5,k5_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X5,X7)
        | r2_hidden(X5,X6)
        | r2_hidden(X5,k5_xboole_0(X6,X7)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_7,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( X1 = esk2_0
    | r2_hidden(esk1_2(X1,esk2_0),esk3_0)
    | r2_hidden(esk1_2(X1,esk2_0),esk4_0)
    | r2_hidden(esk1_2(X1,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( k5_xboole_0(X1,X2) = esk2_0
    | r2_hidden(esk1_2(k5_xboole_0(X1,X2),esk2_0),esk4_0)
    | r2_hidden(esk1_2(k5_xboole_0(X1,X2),esk2_0),esk3_0)
    | r2_hidden(esk1_2(k5_xboole_0(X1,X2),esk2_0),X2)
    | r2_hidden(esk1_2(k5_xboole_0(X1,X2),esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( k5_xboole_0(X1,esk4_0) = esk2_0
    | r2_hidden(esk1_2(k5_xboole_0(X1,esk4_0),esk2_0),esk4_0)
    | r2_hidden(esk1_2(k5_xboole_0(X1,esk4_0),esk2_0),esk3_0)
    | r2_hidden(esk1_2(k5_xboole_0(X1,esk4_0),esk2_0),X1) ),
    inference(ef,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( k5_xboole_0(X1,esk4_0) = esk2_0
    | r2_hidden(esk1_2(k5_xboole_0(X1,esk4_0),esk2_0),esk2_0)
    | r2_hidden(esk1_2(k5_xboole_0(X1,esk4_0),esk2_0),esk3_0)
    | r2_hidden(esk1_2(k5_xboole_0(X1,esk4_0),esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_15,negated_conjecture,
    ( esk2_0 != k5_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk1_2(k5_xboole_0(esk3_0,esk4_0),esk2_0),esk3_0)
    | r2_hidden(esk1_2(k5_xboole_0(esk3_0,esk4_0),esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_14]),c_0_15])).

cnf(c_0_19,plain,
    ( k5_xboole_0(X1,X2) = X3
    | r2_hidden(esk1_2(k5_xboole_0(X1,X2),X3),X3)
    | ~ r2_hidden(esk1_2(k5_xboole_0(X1,X2),X3),X2)
    | ~ r2_hidden(esk1_2(k5_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk1_2(k5_xboole_0(esk3_0,esk4_0),esk2_0),esk2_0)
    | r2_hidden(esk1_2(k5_xboole_0(esk3_0,esk4_0),esk2_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X3,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,plain,
    ( X1 = X2
    | ~ r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk1_2(k5_xboole_0(esk3_0,esk4_0),esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_15]),c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( X1 = esk2_0
    | r2_hidden(esk1_2(X1,esk2_0),k5_xboole_0(X2,esk4_0))
    | r2_hidden(esk1_2(X1,esk2_0),esk3_0)
    | r2_hidden(esk1_2(X1,esk2_0),X1)
    | r2_hidden(esk1_2(X1,esk2_0),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(esk1_2(k5_xboole_0(esk3_0,esk4_0),esk2_0),k5_xboole_0(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( k5_xboole_0(X1,esk4_0) = esk2_0
    | r2_hidden(esk1_2(k5_xboole_0(X1,esk4_0),esk2_0),k5_xboole_0(X1,esk4_0))
    | r2_hidden(esk1_2(k5_xboole_0(X1,esk4_0),esk2_0),esk3_0)
    | r2_hidden(esk1_2(k5_xboole_0(X1,esk4_0),esk2_0),X1) ),
    inference(ef,[status(thm)],[c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_2(k5_xboole_0(esk3_0,esk4_0),esk2_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( X1 = esk2_0
    | r2_hidden(esk1_2(X1,esk2_0),X1)
    | ~ r2_hidden(esk1_2(X1,esk2_0),esk3_0)
    | ~ r2_hidden(esk1_2(X1,esk2_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_8])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_2(k5_xboole_0(esk3_0,esk4_0),esk2_0),k5_xboole_0(esk3_0,X1))
    | r2_hidden(esk1_2(k5_xboole_0(esk3_0,esk4_0),esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(esk1_2(k5_xboole_0(esk3_0,esk4_0),esk2_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_29]),c_0_15]),c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_31]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:00:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.52  # AutoSched0-Mode selected heuristic G_E___008_C45_F1_PI_S5PRR_SE_Q4_CS_SP_S4S
% 0.19/0.52  # and selection function SelectNewComplexAHPNS.
% 0.19/0.52  #
% 0.19/0.52  # Preprocessing time       : 0.026 s
% 0.19/0.52  
% 0.19/0.52  # Proof found!
% 0.19/0.52  # SZS status Theorem
% 0.19/0.52  # SZS output start CNFRefutation
% 0.19/0.52  fof(t2_xboole_0, conjecture, ![X1, X2, X3]:(![X4]:(~(r2_hidden(X4,X1))<=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X1=k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_0)).
% 0.19/0.52  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 0.19/0.52  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.19/0.52  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3]:(![X4]:(~(r2_hidden(X4,X1))<=>(r2_hidden(X4,X2)<=>r2_hidden(X4,X3)))=>X1=k5_xboole_0(X2,X3))), inference(assume_negation,[status(cth)],[t2_xboole_0])).
% 0.19/0.52  fof(c_0_4, negated_conjecture, ![X14]:((((~r2_hidden(X14,esk3_0)|r2_hidden(X14,esk4_0)|r2_hidden(X14,esk2_0))&(~r2_hidden(X14,esk4_0)|r2_hidden(X14,esk3_0)|r2_hidden(X14,esk2_0)))&((~r2_hidden(X14,esk3_0)|~r2_hidden(X14,esk4_0)|~r2_hidden(X14,esk2_0))&(r2_hidden(X14,esk3_0)|r2_hidden(X14,esk4_0)|~r2_hidden(X14,esk2_0))))&esk2_0!=k5_xboole_0(esk3_0,esk4_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])])).
% 0.19/0.52  fof(c_0_5, plain, ![X8, X9]:((~r2_hidden(esk1_2(X8,X9),X8)|~r2_hidden(esk1_2(X8,X9),X9)|X8=X9)&(r2_hidden(esk1_2(X8,X9),X8)|r2_hidden(esk1_2(X8,X9),X9)|X8=X9)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.19/0.52  fof(c_0_6, plain, ![X5, X6, X7]:(((~r2_hidden(X5,X6)|~r2_hidden(X5,X7)|~r2_hidden(X5,k5_xboole_0(X6,X7)))&(r2_hidden(X5,X6)|r2_hidden(X5,X7)|~r2_hidden(X5,k5_xboole_0(X6,X7))))&((~r2_hidden(X5,X6)|r2_hidden(X5,X7)|r2_hidden(X5,k5_xboole_0(X6,X7)))&(~r2_hidden(X5,X7)|r2_hidden(X5,X6)|r2_hidden(X5,k5_xboole_0(X6,X7))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.19/0.52  cnf(c_0_7, negated_conjecture, (r2_hidden(X1,esk3_0)|r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.52  cnf(c_0_8, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.52  cnf(c_0_9, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.52  cnf(c_0_10, negated_conjecture, (X1=esk2_0|r2_hidden(esk1_2(X1,esk2_0),esk3_0)|r2_hidden(esk1_2(X1,esk2_0),esk4_0)|r2_hidden(esk1_2(X1,esk2_0),X1)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.19/0.52  cnf(c_0_11, negated_conjecture, (k5_xboole_0(X1,X2)=esk2_0|r2_hidden(esk1_2(k5_xboole_0(X1,X2),esk2_0),esk4_0)|r2_hidden(esk1_2(k5_xboole_0(X1,X2),esk2_0),esk3_0)|r2_hidden(esk1_2(k5_xboole_0(X1,X2),esk2_0),X2)|r2_hidden(esk1_2(k5_xboole_0(X1,X2),esk2_0),X1)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.19/0.52  cnf(c_0_12, negated_conjecture, (r2_hidden(X1,esk3_0)|r2_hidden(X1,esk2_0)|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.52  cnf(c_0_13, negated_conjecture, (k5_xboole_0(X1,esk4_0)=esk2_0|r2_hidden(esk1_2(k5_xboole_0(X1,esk4_0),esk2_0),esk4_0)|r2_hidden(esk1_2(k5_xboole_0(X1,esk4_0),esk2_0),esk3_0)|r2_hidden(esk1_2(k5_xboole_0(X1,esk4_0),esk2_0),X1)), inference(ef,[status(thm)],[c_0_11])).
% 0.19/0.52  cnf(c_0_14, negated_conjecture, (k5_xboole_0(X1,esk4_0)=esk2_0|r2_hidden(esk1_2(k5_xboole_0(X1,esk4_0),esk2_0),esk2_0)|r2_hidden(esk1_2(k5_xboole_0(X1,esk4_0),esk2_0),esk3_0)|r2_hidden(esk1_2(k5_xboole_0(X1,esk4_0),esk2_0),X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.52  cnf(c_0_15, negated_conjecture, (esk2_0!=k5_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.52  cnf(c_0_16, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.52  cnf(c_0_17, negated_conjecture, (r2_hidden(X1,esk4_0)|r2_hidden(X1,esk2_0)|~r2_hidden(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.52  cnf(c_0_18, negated_conjecture, (r2_hidden(esk1_2(k5_xboole_0(esk3_0,esk4_0),esk2_0),esk3_0)|r2_hidden(esk1_2(k5_xboole_0(esk3_0,esk4_0),esk2_0),esk2_0)), inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_14]), c_0_15])).
% 0.19/0.52  cnf(c_0_19, plain, (k5_xboole_0(X1,X2)=X3|r2_hidden(esk1_2(k5_xboole_0(X1,X2),X3),X3)|~r2_hidden(esk1_2(k5_xboole_0(X1,X2),X3),X2)|~r2_hidden(esk1_2(k5_xboole_0(X1,X2),X3),X1)), inference(spm,[status(thm)],[c_0_16, c_0_8])).
% 0.19/0.52  cnf(c_0_20, negated_conjecture, (r2_hidden(esk1_2(k5_xboole_0(esk3_0,esk4_0),esk2_0),esk2_0)|r2_hidden(esk1_2(k5_xboole_0(esk3_0,esk4_0),esk2_0),esk4_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.52  cnf(c_0_21, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X3,X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.52  cnf(c_0_22, plain, (X1=X2|~r2_hidden(esk1_2(X1,X2),X1)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.52  cnf(c_0_23, negated_conjecture, (r2_hidden(esk1_2(k5_xboole_0(esk3_0,esk4_0),esk2_0),esk2_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_15]), c_0_18])).
% 0.19/0.52  cnf(c_0_24, negated_conjecture, (X1=esk2_0|r2_hidden(esk1_2(X1,esk2_0),k5_xboole_0(X2,esk4_0))|r2_hidden(esk1_2(X1,esk2_0),esk3_0)|r2_hidden(esk1_2(X1,esk2_0),X1)|r2_hidden(esk1_2(X1,esk2_0),X2)), inference(spm,[status(thm)],[c_0_21, c_0_10])).
% 0.19/0.52  cnf(c_0_25, negated_conjecture, (~r2_hidden(esk1_2(k5_xboole_0(esk3_0,esk4_0),esk2_0),k5_xboole_0(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_15])).
% 0.19/0.52  cnf(c_0_26, negated_conjecture, (k5_xboole_0(X1,esk4_0)=esk2_0|r2_hidden(esk1_2(k5_xboole_0(X1,esk4_0),esk2_0),k5_xboole_0(X1,esk4_0))|r2_hidden(esk1_2(k5_xboole_0(X1,esk4_0),esk2_0),esk3_0)|r2_hidden(esk1_2(k5_xboole_0(X1,esk4_0),esk2_0),X1)), inference(ef,[status(thm)],[c_0_24])).
% 0.19/0.52  cnf(c_0_27, negated_conjecture, (~r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.52  cnf(c_0_28, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.52  cnf(c_0_29, negated_conjecture, (r2_hidden(esk1_2(k5_xboole_0(esk3_0,esk4_0),esk2_0),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_15])).
% 0.19/0.52  cnf(c_0_30, negated_conjecture, (X1=esk2_0|r2_hidden(esk1_2(X1,esk2_0),X1)|~r2_hidden(esk1_2(X1,esk2_0),esk3_0)|~r2_hidden(esk1_2(X1,esk2_0),esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_8])).
% 0.19/0.52  cnf(c_0_31, negated_conjecture, (r2_hidden(esk1_2(k5_xboole_0(esk3_0,esk4_0),esk2_0),k5_xboole_0(esk3_0,X1))|r2_hidden(esk1_2(k5_xboole_0(esk3_0,esk4_0),esk2_0),X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.52  cnf(c_0_32, negated_conjecture, (~r2_hidden(esk1_2(k5_xboole_0(esk3_0,esk4_0),esk2_0),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_29]), c_0_15]), c_0_25])).
% 0.19/0.52  cnf(c_0_33, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_31]), c_0_32]), ['proof']).
% 0.19/0.52  # SZS output end CNFRefutation
% 0.19/0.52  # Proof object total steps             : 34
% 0.19/0.52  # Proof object clause steps            : 27
% 0.19/0.52  # Proof object formula steps           : 7
% 0.19/0.52  # Proof object conjectures             : 23
% 0.19/0.52  # Proof object clause conjectures      : 20
% 0.19/0.52  # Proof object formula conjectures     : 3
% 0.19/0.52  # Proof object initial clauses used    : 11
% 0.19/0.52  # Proof object initial formulas used   : 3
% 0.19/0.52  # Proof object generating inferences   : 16
% 0.19/0.52  # Proof object simplifying inferences  : 8
% 0.19/0.52  # Training examples: 0 positive, 0 negative
% 0.19/0.52  # Parsed axioms                        : 3
% 0.19/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.52  # Initial clauses                      : 11
% 0.19/0.52  # Removed in clause preprocessing      : 0
% 0.19/0.52  # Initial clauses in saturation        : 11
% 0.19/0.52  # Processed clauses                    : 1648
% 0.19/0.52  # ...of these trivial                  : 2
% 0.19/0.52  # ...subsumed                          : 1125
% 0.19/0.52  # ...remaining for further processing  : 521
% 0.19/0.52  # Other redundant clauses eliminated   : 0
% 0.19/0.52  # Clauses deleted for lack of memory   : 0
% 0.19/0.52  # Backward-subsumed                    : 60
% 0.19/0.52  # Backward-rewritten                   : 55
% 0.19/0.52  # Generated clauses                    : 4614
% 0.19/0.52  # ...of the previous two non-trivial   : 3939
% 0.19/0.52  # Contextual simplify-reflections      : 23
% 0.19/0.52  # Paramodulations                      : 4214
% 0.19/0.52  # Factorizations                       : 400
% 0.19/0.52  # Equation resolutions                 : 0
% 0.19/0.52  # Propositional unsat checks           : 0
% 0.19/0.52  #    Propositional check models        : 0
% 0.19/0.52  #    Propositional check unsatisfiable : 0
% 0.19/0.52  #    Propositional clauses             : 0
% 0.19/0.52  #    Propositional clauses after purity: 0
% 0.19/0.52  #    Propositional unsat core size     : 0
% 0.19/0.52  #    Propositional preprocessing time  : 0.000
% 0.19/0.52  #    Propositional encoding time       : 0.000
% 0.19/0.52  #    Propositional solver time         : 0.000
% 0.19/0.52  #    Success case prop preproc time    : 0.000
% 0.19/0.52  #    Success case prop encoding time   : 0.000
% 0.19/0.52  #    Success case prop solver time     : 0.000
% 0.19/0.52  # Current number of processed clauses  : 406
% 0.19/0.52  #    Positive orientable unit clauses  : 6
% 0.19/0.52  #    Positive unorientable unit clauses: 0
% 0.19/0.52  #    Negative unit clauses             : 3
% 0.19/0.52  #    Non-unit-clauses                  : 397
% 0.19/0.52  # Current number of unprocessed clauses: 2219
% 0.19/0.52  # ...number of literals in the above   : 11636
% 0.19/0.52  # Current number of archived formulas  : 0
% 0.19/0.52  # Current number of archived clauses   : 115
% 0.19/0.52  # Clause-clause subsumption calls (NU) : 52690
% 0.19/0.52  # Rec. Clause-clause subsumption calls : 4121
% 0.19/0.52  # Non-unit clause-clause subsumptions  : 1207
% 0.19/0.52  # Unit Clause-clause subsumption calls : 823
% 0.19/0.52  # Rewrite failures with RHS unbound    : 0
% 0.19/0.52  # BW rewrite match attempts            : 15
% 0.19/0.52  # BW rewrite match successes           : 5
% 0.19/0.52  # Condensation attempts                : 0
% 0.19/0.52  # Condensation successes               : 0
% 0.19/0.52  # Termbank termtop insertions          : 114253
% 0.19/0.52  
% 0.19/0.52  # -------------------------------------------------
% 0.19/0.52  # User time                : 0.163 s
% 0.19/0.52  # System time              : 0.009 s
% 0.19/0.52  # Total time               : 0.172 s
% 0.19/0.52  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
