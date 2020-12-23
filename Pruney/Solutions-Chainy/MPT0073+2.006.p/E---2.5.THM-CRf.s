%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:43 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 266 expanded)
%              Number of clauses        :   23 ( 130 expanded)
%              Number of leaves         :    4 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :   98 (1177 expanded)
%              Number of equality atoms :   39 ( 430 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t66_xboole_1,conjecture,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(c_0_4,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_5,plain,(
    ! [X16] : k3_xboole_0(X16,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_6,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ~ ( ~ r1_xboole_0(X1,X1)
            & X1 = k1_xboole_0 )
        & ~ ( X1 != k1_xboole_0
            & r1_xboole_0(X1,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t66_xboole_1])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_xboole_0
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

fof(c_0_10,plain,(
    ! [X14,X15] :
      ( ( ~ r1_xboole_0(X14,X15)
        | k3_xboole_0(X14,X15) = k1_xboole_0 )
      & ( k3_xboole_0(X14,X15) != k1_xboole_0
        | r1_xboole_0(X14,X15) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_11,negated_conjecture,
    ( ( esk2_0 != k1_xboole_0
      | ~ r1_xboole_0(esk2_0,esk2_0) )
    & ( r1_xboole_0(esk2_0,esk2_0)
      | ~ r1_xboole_0(esk2_0,esk2_0) )
    & ( esk2_0 != k1_xboole_0
      | esk2_0 = k1_xboole_0 )
    & ( r1_xboole_0(esk2_0,esk2_0)
      | esk2_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk2_0)
    | esk2_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(X2,k1_xboole_0,X1),X1)
    | r2_hidden(esk1_3(X2,k1_xboole_0,X1),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_7])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk2_0) = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(X2,k1_xboole_0,X1),X1) ),
    inference(ef,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k1_xboole_0
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_9])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(esk1_3(X2,k1_xboole_0,X1),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_7])]),c_0_12])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk1_3(X3,k1_xboole_0,k3_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ r1_xboole_0(esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_20]),c_0_23])).

cnf(c_0_30,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_29]),c_0_29]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:15:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.14/0.39  # and selection function SelectNewComplexAHP.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.039 s
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.14/0.39  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.14/0.39  fof(t66_xboole_1, conjecture, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.14/0.39  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.14/0.39  fof(c_0_4, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.14/0.39  fof(c_0_5, plain, ![X16]:k3_xboole_0(X16,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.14/0.39  cnf(c_0_6, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.14/0.39  cnf(c_0_7, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.39  fof(c_0_8, negated_conjecture, ~(![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1))))), inference(assume_negation,[status(cth)],[t66_xboole_1])).
% 0.14/0.39  cnf(c_0_9, plain, (r2_hidden(X1,X2)|X3!=k1_xboole_0|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.14/0.39  fof(c_0_10, plain, ![X14, X15]:((~r1_xboole_0(X14,X15)|k3_xboole_0(X14,X15)=k1_xboole_0)&(k3_xboole_0(X14,X15)!=k1_xboole_0|r1_xboole_0(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.14/0.39  fof(c_0_11, negated_conjecture, (((esk2_0!=k1_xboole_0|~r1_xboole_0(esk2_0,esk2_0))&(r1_xboole_0(esk2_0,esk2_0)|~r1_xboole_0(esk2_0,esk2_0)))&((esk2_0!=k1_xboole_0|esk2_0=k1_xboole_0)&(r1_xboole_0(esk2_0,esk2_0)|esk2_0=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).
% 0.14/0.39  cnf(c_0_12, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(er,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_13, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.14/0.39  cnf(c_0_14, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_15, negated_conjecture, (r1_xboole_0(esk2_0,esk2_0)|esk2_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_16, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(X2,k1_xboole_0,X1),X1)|r2_hidden(esk1_3(X2,k1_xboole_0,X1),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_7])).
% 0.14/0.39  cnf(c_0_17, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.14/0.39  cnf(c_0_18, negated_conjecture, (k3_xboole_0(esk2_0,esk2_0)=k1_xboole_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.14/0.39  cnf(c_0_19, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.14/0.39  cnf(c_0_20, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(X2,k1_xboole_0,X1),X1)), inference(ef,[status(thm)],[c_0_16])).
% 0.14/0.39  cnf(c_0_21, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_6])).
% 0.14/0.39  cnf(c_0_22, negated_conjecture, (r2_hidden(X1,X2)|X2!=k1_xboole_0|~r2_hidden(X1,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_9])).
% 0.14/0.39  cnf(c_0_23, plain, (X1=k1_xboole_0|~r2_hidden(esk1_3(X2,k1_xboole_0,X1),k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_7])]), c_0_12])).
% 0.14/0.39  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk1_3(X3,k1_xboole_0,k3_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_21, c_0_20])).
% 0.14/0.39  cnf(c_0_25, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,esk2_0)), inference(er,[status(thm)],[c_0_22])).
% 0.14/0.39  cnf(c_0_26, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_27, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.39  cnf(c_0_28, negated_conjecture, (esk2_0!=k1_xboole_0|~r1_xboole_0(esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_29, negated_conjecture, (esk2_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_20]), c_0_23])).
% 0.14/0.39  cnf(c_0_30, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.14/0.39  cnf(c_0_31, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_29]), c_0_29]), c_0_30])]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 32
% 0.14/0.39  # Proof object clause steps            : 23
% 0.14/0.39  # Proof object formula steps           : 9
% 0.14/0.39  # Proof object conjectures             : 10
% 0.14/0.39  # Proof object clause conjectures      : 7
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 9
% 0.14/0.39  # Proof object initial formulas used   : 4
% 0.14/0.39  # Proof object generating inferences   : 13
% 0.14/0.39  # Proof object simplifying inferences  : 11
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 4
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 13
% 0.14/0.39  # Removed in clause preprocessing      : 2
% 0.14/0.39  # Initial clauses in saturation        : 11
% 0.14/0.39  # Processed clauses                    : 48
% 0.14/0.39  # ...of these trivial                  : 4
% 0.14/0.39  # ...subsumed                          : 13
% 0.14/0.39  # ...remaining for further processing  : 31
% 0.14/0.39  # Other redundant clauses eliminated   : 0
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 1
% 0.14/0.39  # Backward-rewritten                   : 6
% 0.14/0.39  # Generated clauses                    : 99
% 0.14/0.39  # ...of the previous two non-trivial   : 91
% 0.14/0.39  # Contextual simplify-reflections      : 3
% 0.14/0.39  # Paramodulations                      : 88
% 0.14/0.39  # Factorizations                       : 6
% 0.14/0.39  # Equation resolutions                 : 5
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 24
% 0.14/0.39  #    Positive orientable unit clauses  : 5
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 0
% 0.14/0.39  #    Non-unit-clauses                  : 19
% 0.14/0.39  # Current number of unprocessed clauses: 52
% 0.14/0.39  # ...number of literals in the above   : 147
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 7
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 70
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 61
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 17
% 0.14/0.39  # Unit Clause-clause subsumption calls : 5
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 2
% 0.14/0.39  # BW rewrite match successes           : 2
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 1799
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.043 s
% 0.14/0.39  # System time              : 0.004 s
% 0.14/0.39  # Total time               : 0.047 s
% 0.14/0.39  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
