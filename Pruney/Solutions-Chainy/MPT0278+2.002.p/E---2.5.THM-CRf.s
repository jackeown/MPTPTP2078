%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:07 EST 2020

% Result     : Theorem 0.82s
% Output     : CNFRefutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   35 (  57 expanded)
%              Number of clauses        :   22 (  27 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :   10
%              Number of atoms          :   78 ( 148 expanded)
%              Number of equality atoms :   15 (  26 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t79_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

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
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | r1_tarski(X12,k2_xboole_0(X14,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_8,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X17,X18,X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X19,X18)
        | r1_tarski(X19,X17)
        | X18 != k1_zfmisc_1(X17) )
      & ( ~ r1_tarski(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k1_zfmisc_1(X17) )
      & ( ~ r2_hidden(esk2_2(X21,X22),X22)
        | ~ r1_tarski(esk2_2(X21,X22),X21)
        | X22 = k1_zfmisc_1(X21) )
      & ( r2_hidden(esk2_2(X21,X22),X22)
        | r1_tarski(esk2_2(X21,X22),X21)
        | X22 = k1_zfmisc_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_15,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_16,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k2_xboole_0(X15,X16) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_13])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,X2)
       => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    inference(assume_negation,[status(cth)],[t79_zfmisc_1])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_11,c_0_14])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r1_tarski(esk1_2(k1_zfmisc_1(X1),X2),X1)
    | r1_tarski(k1_zfmisc_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_9])).

fof(c_0_23,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,esk1_2(k1_zfmisc_1(X1),X2)) = X1
    | r1_tarski(k1_zfmisc_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,plain,
    ( r1_tarski(esk1_2(k1_zfmisc_1(X1),X2),k2_xboole_0(X1,X3))
    | r1_tarski(k1_zfmisc_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_26])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk1_2(k1_zfmisc_1(esk3_0),X1),esk4_0)
    | r1_tarski(k1_zfmisc_1(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk1_2(k1_zfmisc_1(esk3_0),X1),k1_zfmisc_1(esk4_0))
    | r1_tarski(k1_zfmisc_1(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_32]),c_0_33]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.31  % Computer   : n001.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.16/0.31  % WCLimit    : 600
% 0.16/0.31  % DateTime   : Tue Dec  1 17:26:00 EST 2020
% 0.16/0.31  % CPUTime    : 
% 0.16/0.32  # Version: 2.5pre002
% 0.16/0.32  # No SInE strategy applied
% 0.16/0.32  # Trying AutoSched0 for 299 seconds
% 0.82/1.00  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.82/1.00  # and selection function SelectSmallestOrientable.
% 0.82/1.00  #
% 0.82/1.00  # Preprocessing time       : 0.019 s
% 0.82/1.00  # Presaturation interreduction done
% 0.82/1.00  
% 0.82/1.00  # Proof found!
% 0.82/1.00  # SZS status Theorem
% 0.82/1.00  # SZS output start CNFRefutation
% 0.82/1.00  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.82/1.00  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.82/1.00  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.82/1.00  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.82/1.00  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.82/1.00  fof(t79_zfmisc_1, conjecture, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 0.82/1.00  fof(c_0_6, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.82/1.00  fof(c_0_7, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|r1_tarski(X12,k2_xboole_0(X14,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.82/1.00  cnf(c_0_8, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.82/1.00  cnf(c_0_9, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.82/1.00  fof(c_0_10, plain, ![X17, X18, X19, X20, X21, X22]:(((~r2_hidden(X19,X18)|r1_tarski(X19,X17)|X18!=k1_zfmisc_1(X17))&(~r1_tarski(X20,X17)|r2_hidden(X20,X18)|X18!=k1_zfmisc_1(X17)))&((~r2_hidden(esk2_2(X21,X22),X22)|~r1_tarski(esk2_2(X21,X22),X21)|X22=k1_zfmisc_1(X21))&(r2_hidden(esk2_2(X21,X22),X22)|r1_tarski(esk2_2(X21,X22),X21)|X22=k1_zfmisc_1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.82/1.00  cnf(c_0_11, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.82/1.00  cnf(c_0_12, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.82/1.00  cnf(c_0_13, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.82/1.00  cnf(c_0_14, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.82/1.00  fof(c_0_15, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.82/1.00  fof(c_0_16, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k2_xboole_0(X15,X16)=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.82/1.00  cnf(c_0_17, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_13])).
% 0.82/1.00  fof(c_0_18, negated_conjecture, ~(![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)))), inference(assume_negation,[status(cth)],[t79_zfmisc_1])).
% 0.82/1.00  cnf(c_0_19, plain, (r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_11, c_0_14])).
% 0.82/1.00  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.82/1.00  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.82/1.00  cnf(c_0_22, plain, (r1_tarski(esk1_2(k1_zfmisc_1(X1),X2),X1)|r1_tarski(k1_zfmisc_1(X1),X2)), inference(spm,[status(thm)],[c_0_17, c_0_9])).
% 0.82/1.00  fof(c_0_23, negated_conjecture, (r1_tarski(esk3_0,esk4_0)&~r1_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.82/1.00  cnf(c_0_24, plain, (r1_tarski(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.82/1.00  cnf(c_0_25, plain, (k2_xboole_0(X1,esk1_2(k1_zfmisc_1(X1),X2))=X1|r1_tarski(k1_zfmisc_1(X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_20])).
% 0.82/1.00  cnf(c_0_26, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.82/1.00  cnf(c_0_27, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.82/1.00  cnf(c_0_28, plain, (r1_tarski(esk1_2(k1_zfmisc_1(X1),X2),k2_xboole_0(X1,X3))|r1_tarski(k1_zfmisc_1(X1),X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.82/1.00  cnf(c_0_29, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_21, c_0_26])).
% 0.82/1.00  cnf(c_0_30, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_27])).
% 0.82/1.00  cnf(c_0_31, negated_conjecture, (r1_tarski(esk1_2(k1_zfmisc_1(esk3_0),X1),esk4_0)|r1_tarski(k1_zfmisc_1(esk3_0),X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.82/1.00  cnf(c_0_32, negated_conjecture, (r2_hidden(esk1_2(k1_zfmisc_1(esk3_0),X1),k1_zfmisc_1(esk4_0))|r1_tarski(k1_zfmisc_1(esk3_0),X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.82/1.00  cnf(c_0_33, negated_conjecture, (~r1_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.82/1.00  cnf(c_0_34, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_32]), c_0_33]), ['proof']).
% 0.82/1.00  # SZS output end CNFRefutation
% 0.82/1.00  # Proof object total steps             : 35
% 0.82/1.00  # Proof object clause steps            : 22
% 0.82/1.00  # Proof object formula steps           : 13
% 0.82/1.00  # Proof object conjectures             : 9
% 0.82/1.00  # Proof object clause conjectures      : 6
% 0.82/1.00  # Proof object formula conjectures     : 3
% 0.82/1.00  # Proof object initial clauses used    : 9
% 0.82/1.00  # Proof object initial formulas used   : 6
% 0.82/1.00  # Proof object generating inferences   : 11
% 0.82/1.00  # Proof object simplifying inferences  : 4
% 0.82/1.00  # Training examples: 0 positive, 0 negative
% 0.82/1.00  # Parsed axioms                        : 6
% 0.82/1.00  # Removed by relevancy pruning/SinE    : 0
% 0.82/1.00  # Initial clauses                      : 12
% 0.82/1.00  # Removed in clause preprocessing      : 0
% 0.82/1.00  # Initial clauses in saturation        : 12
% 0.82/1.00  # Processed clauses                    : 4845
% 0.82/1.00  # ...of these trivial                  : 251
% 0.82/1.00  # ...subsumed                          : 3826
% 0.82/1.00  # ...remaining for further processing  : 768
% 0.82/1.00  # Other redundant clauses eliminated   : 2
% 0.82/1.00  # Clauses deleted for lack of memory   : 0
% 0.82/1.00  # Backward-subsumed                    : 10
% 0.82/1.00  # Backward-rewritten                   : 0
% 0.82/1.00  # Generated clauses                    : 50791
% 0.82/1.00  # ...of the previous two non-trivial   : 45776
% 0.82/1.00  # Contextual simplify-reflections      : 0
% 0.82/1.00  # Paramodulations                      : 50595
% 0.82/1.00  # Factorizations                       : 194
% 0.82/1.00  # Equation resolutions                 : 2
% 0.82/1.00  # Propositional unsat checks           : 0
% 0.82/1.00  #    Propositional check models        : 0
% 0.82/1.00  #    Propositional check unsatisfiable : 0
% 0.82/1.00  #    Propositional clauses             : 0
% 0.82/1.00  #    Propositional clauses after purity: 0
% 0.82/1.00  #    Propositional unsat core size     : 0
% 0.82/1.00  #    Propositional preprocessing time  : 0.000
% 0.82/1.00  #    Propositional encoding time       : 0.000
% 0.82/1.00  #    Propositional solver time         : 0.000
% 0.82/1.00  #    Success case prop preproc time    : 0.000
% 0.82/1.00  #    Success case prop encoding time   : 0.000
% 0.82/1.00  #    Success case prop solver time     : 0.000
% 0.82/1.00  # Current number of processed clauses  : 744
% 0.82/1.00  #    Positive orientable unit clauses  : 106
% 0.82/1.00  #    Positive unorientable unit clauses: 1
% 0.82/1.00  #    Negative unit clauses             : 1
% 0.82/1.00  #    Non-unit-clauses                  : 636
% 0.82/1.00  # Current number of unprocessed clauses: 40948
% 0.82/1.00  # ...number of literals in the above   : 274641
% 0.82/1.00  # Current number of archived formulas  : 0
% 0.82/1.00  # Current number of archived clauses   : 22
% 0.82/1.00  # Clause-clause subsumption calls (NU) : 150979
% 0.82/1.00  # Rec. Clause-clause subsumption calls : 76687
% 0.82/1.00  # Non-unit clause-clause subsumptions  : 3836
% 0.82/1.00  # Unit Clause-clause subsumption calls : 1808
% 0.82/1.00  # Rewrite failures with RHS unbound    : 0
% 0.82/1.00  # BW rewrite match attempts            : 615
% 0.82/1.00  # BW rewrite match successes           : 4
% 0.82/1.00  # Condensation attempts                : 0
% 0.82/1.00  # Condensation successes               : 0
% 0.82/1.00  # Termbank termtop insertions          : 1222772
% 0.82/1.00  
% 0.82/1.00  # -------------------------------------------------
% 0.82/1.00  # User time                : 0.655 s
% 0.82/1.00  # System time              : 0.031 s
% 0.82/1.00  # Total time               : 0.686 s
% 0.82/1.00  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
