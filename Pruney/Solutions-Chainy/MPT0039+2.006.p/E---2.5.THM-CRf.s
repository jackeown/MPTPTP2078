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
% DateTime   : Thu Dec  3 10:32:01 EST 2020

% Result     : Theorem 15.59s
% Output     : CNFRefutation 15.59s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 261 expanded)
%              Number of clauses        :   29 ( 121 expanded)
%              Number of leaves         :    3 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :   96 (1308 expanded)
%              Number of equality atoms :   37 ( 484 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_xboole_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t32_xboole_1])).

fof(c_0_4,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_5,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k4_xboole_0(esk4_0,esk3_0)
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k4_xboole_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( X1 != k4_xboole_0(esk3_0,esk4_0)
    | ~ r2_hidden(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])).

fof(c_0_10,plain,(
    ! [X14] :
      ( X14 = k1_xboole_0
      | r2_hidden(esk2_1(X14),X14) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_16,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,plain,
    ( X1 = k4_xboole_0(X2,X3)
    | r2_hidden(esk1_3(X2,X3,X1),k4_xboole_0(X2,X4))
    | r2_hidden(esk1_3(X2,X3,X1),X1)
    | r2_hidden(esk1_3(X2,X3,X1),X4) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_9,c_0_16])).

cnf(c_0_22,plain,
    ( X1 = k4_xboole_0(X2,k4_xboole_0(X2,X3))
    | r2_hidden(esk1_3(X2,k4_xboole_0(X2,X3),X1),X3)
    | r2_hidden(esk1_3(X2,k4_xboole_0(X2,X3),X1),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_12,c_0_16])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | X2 != k1_xboole_0
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_16]),c_0_21])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X2
    | r2_hidden(esk1_3(X1,k4_xboole_0(X1,X2),X2),X2) ),
    inference(ef,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_7,c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_3(esk4_0,k1_xboole_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( k4_xboole_0(X1,X2) = esk3_0
    | r2_hidden(esk1_3(X1,X2,esk3_0),esk4_0)
    | r2_hidden(esk1_3(X1,X2,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(esk1_3(esk4_0,k1_xboole_0,esk3_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_31]),c_0_28]),c_0_29]),c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( k4_xboole_0(esk4_0,X1) = esk3_0
    | r2_hidden(esk1_3(esk4_0,X1,esk3_0),esk4_0) ),
    inference(ef,[status(thm)],[c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_28]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n022.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:14:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 15.59/15.76  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 15.59/15.76  # and selection function SelectNewComplexAHP.
% 15.59/15.76  #
% 15.59/15.76  # Preprocessing time       : 0.026 s
% 15.59/15.76  
% 15.59/15.76  # Proof found!
% 15.59/15.76  # SZS status Theorem
% 15.59/15.76  # SZS output start CNFRefutation
% 15.59/15.76  fof(t32_xboole_1, conjecture, ![X1, X2]:(k4_xboole_0(X1,X2)=k4_xboole_0(X2,X1)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 15.59/15.76  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 15.59/15.76  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 15.59/15.76  fof(c_0_3, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(X1,X2)=k4_xboole_0(X2,X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t32_xboole_1])).
% 15.59/15.76  fof(c_0_4, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 15.59/15.76  fof(c_0_5, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k4_xboole_0(esk4_0,esk3_0)&esk3_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 15.59/15.76  cnf(c_0_6, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 15.59/15.76  cnf(c_0_7, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k4_xboole_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 15.59/15.76  cnf(c_0_8, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 15.59/15.76  cnf(c_0_9, negated_conjecture, (X1!=k4_xboole_0(esk3_0,esk4_0)|~r2_hidden(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_7]), c_0_8])).
% 15.59/15.76  fof(c_0_10, plain, ![X14]:(X14=k1_xboole_0|r2_hidden(esk2_1(X14),X14)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 15.59/15.76  cnf(c_0_11, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 15.59/15.76  cnf(c_0_12, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk3_0,esk4_0))), inference(er,[status(thm)],[c_0_9])).
% 15.59/15.76  cnf(c_0_13, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 15.59/15.76  cnf(c_0_14, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_11])).
% 15.59/15.76  cnf(c_0_15, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 15.59/15.76  cnf(c_0_16, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 15.59/15.76  cnf(c_0_17, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 15.59/15.76  cnf(c_0_18, plain, (X1=k4_xboole_0(X2,X3)|r2_hidden(esk1_3(X2,X3,X1),k4_xboole_0(X2,X4))|r2_hidden(esk1_3(X2,X3,X1),X1)|r2_hidden(esk1_3(X2,X3,X1),X4)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 15.59/15.76  cnf(c_0_19, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 15.59/15.76  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_15])).
% 15.59/15.76  cnf(c_0_21, negated_conjecture, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_9, c_0_16])).
% 15.59/15.76  cnf(c_0_22, plain, (X1=k4_xboole_0(X2,k4_xboole_0(X2,X3))|r2_hidden(esk1_3(X2,k4_xboole_0(X2,X3),X1),X3)|r2_hidden(esk1_3(X2,k4_xboole_0(X2,X3),X1),X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 15.59/15.76  cnf(c_0_23, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_12, c_0_16])).
% 15.59/15.76  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_20])).
% 15.59/15.76  cnf(c_0_25, negated_conjecture, (r2_hidden(X1,esk4_0)|X2!=k1_xboole_0|~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_16]), c_0_21])).
% 15.59/15.76  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X2|r2_hidden(esk1_3(X1,k4_xboole_0(X1,X2),X2),X2)), inference(ef,[status(thm)],[c_0_22])).
% 15.59/15.76  cnf(c_0_27, negated_conjecture, (k4_xboole_0(esk4_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_7, c_0_16])).
% 15.59/15.76  cnf(c_0_28, negated_conjecture, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 15.59/15.76  cnf(c_0_29, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 15.59/15.76  cnf(c_0_30, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(er,[status(thm)],[c_0_25])).
% 15.59/15.76  cnf(c_0_31, negated_conjecture, (r2_hidden(esk1_3(esk4_0,k1_xboole_0,esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])).
% 15.59/15.76  cnf(c_0_32, negated_conjecture, (k4_xboole_0(X1,X2)=esk3_0|r2_hidden(esk1_3(X1,X2,esk3_0),esk4_0)|r2_hidden(esk1_3(X1,X2,esk3_0),X1)), inference(spm,[status(thm)],[c_0_30, c_0_15])).
% 15.59/15.76  cnf(c_0_33, negated_conjecture, (~r2_hidden(esk1_3(esk4_0,k1_xboole_0,esk3_0),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_31]), c_0_28]), c_0_29]), c_0_23])).
% 15.59/15.76  cnf(c_0_34, negated_conjecture, (k4_xboole_0(esk4_0,X1)=esk3_0|r2_hidden(esk1_3(esk4_0,X1,esk3_0),esk4_0)), inference(ef,[status(thm)],[c_0_32])).
% 15.59/15.76  cnf(c_0_35, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_28]), c_0_29]), ['proof']).
% 15.59/15.76  # SZS output end CNFRefutation
% 15.59/15.76  # Proof object total steps             : 36
% 15.59/15.76  # Proof object clause steps            : 29
% 15.59/15.76  # Proof object formula steps           : 7
% 15.59/15.76  # Proof object conjectures             : 19
% 15.59/15.76  # Proof object clause conjectures      : 16
% 15.59/15.76  # Proof object formula conjectures     : 3
% 15.59/15.76  # Proof object initial clauses used    : 9
% 15.59/15.76  # Proof object initial formulas used   : 3
% 15.59/15.76  # Proof object generating inferences   : 17
% 15.59/15.76  # Proof object simplifying inferences  : 13
% 15.59/15.76  # Training examples: 0 positive, 0 negative
% 15.59/15.76  # Parsed axioms                        : 3
% 15.59/15.76  # Removed by relevancy pruning/SinE    : 0
% 15.59/15.76  # Initial clauses                      : 9
% 15.59/15.76  # Removed in clause preprocessing      : 0
% 15.59/15.76  # Initial clauses in saturation        : 9
% 15.59/15.76  # Processed clauses                    : 244947
% 15.59/15.76  # ...of these trivial                  : 941
% 15.59/15.76  # ...subsumed                          : 238643
% 15.59/15.76  # ...remaining for further processing  : 5363
% 15.59/15.76  # Other redundant clauses eliminated   : 1338
% 15.59/15.76  # Clauses deleted for lack of memory   : 0
% 15.59/15.76  # Backward-subsumed                    : 308
% 15.59/15.76  # Backward-rewritten                   : 113
% 15.59/15.76  # Generated clauses                    : 2477511
% 15.59/15.76  # ...of the previous two non-trivial   : 2258504
% 15.59/15.76  # Contextual simplify-reflections      : 242
% 15.59/15.76  # Paramodulations                      : 2473353
% 15.59/15.76  # Factorizations                       : 196
% 15.59/15.76  # Equation resolutions                 : 2392
% 15.59/15.76  # Propositional unsat checks           : 0
% 15.59/15.76  #    Propositional check models        : 0
% 15.59/15.76  #    Propositional check unsatisfiable : 0
% 15.59/15.76  #    Propositional clauses             : 0
% 15.59/15.76  #    Propositional clauses after purity: 0
% 15.59/15.76  #    Propositional unsat core size     : 0
% 15.59/15.76  #    Propositional preprocessing time  : 0.000
% 15.59/15.76  #    Propositional encoding time       : 0.000
% 15.59/15.76  #    Propositional solver time         : 0.000
% 15.59/15.76  #    Success case prop preproc time    : 0.000
% 15.59/15.76  #    Success case prop encoding time   : 0.000
% 15.59/15.76  #    Success case prop solver time     : 0.000
% 15.59/15.76  # Current number of processed clauses  : 4942
% 15.59/15.76  #    Positive orientable unit clauses  : 290
% 15.59/15.76  #    Positive unorientable unit clauses: 0
% 15.59/15.76  #    Negative unit clauses             : 181
% 15.59/15.76  #    Non-unit-clauses                  : 4471
% 15.59/15.76  # Current number of unprocessed clauses: 2003421
% 15.59/15.76  # ...number of literals in the above   : 5953508
% 15.59/15.76  # Current number of archived formulas  : 0
% 15.59/15.76  # Current number of archived clauses   : 421
% 15.59/15.76  # Clause-clause subsumption calls (NU) : 3941280
% 15.59/15.76  # Rec. Clause-clause subsumption calls : 2606940
% 15.59/15.76  # Non-unit clause-clause subsumptions  : 108709
% 15.59/15.76  # Unit Clause-clause subsumption calls : 284223
% 15.59/15.76  # Rewrite failures with RHS unbound    : 0
% 15.59/15.76  # BW rewrite match attempts            : 7015
% 15.59/15.76  # BW rewrite match successes           : 48
% 15.59/15.76  # Condensation attempts                : 0
% 15.59/15.76  # Condensation successes               : 0
% 15.59/15.76  # Termbank termtop insertions          : 46653080
% 15.59/15.83  
% 15.59/15.83  # -------------------------------------------------
% 15.59/15.83  # User time                : 14.768 s
% 15.59/15.83  # System time              : 0.710 s
% 15.59/15.83  # Total time               : 15.478 s
% 15.59/15.83  # Maximum resident set size: 1552 pages
%------------------------------------------------------------------------------
