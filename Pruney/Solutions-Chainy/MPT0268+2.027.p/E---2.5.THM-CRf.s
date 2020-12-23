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
% DateTime   : Thu Dec  3 10:42:21 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 458 expanded)
%              Number of clauses        :   27 ( 207 expanded)
%              Number of leaves         :    5 ( 110 expanded)
%              Depth                    :   13
%              Number of atoms          :  114 (1549 expanded)
%              Number of equality atoms :   43 ( 618 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(l38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    <=> ( ~ r2_hidden(X1,X3)
        & ( r2_hidden(X2,X3)
          | X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(X1,k1_tarski(X2)) = X1
      <=> ~ r2_hidden(X2,X1) ) ),
    inference(assume_negation,[status(cth)],[t65_zfmisc_1])).

fof(c_0_6,negated_conjecture,
    ( ( k4_xboole_0(esk2_0,k1_tarski(esk3_0)) != esk2_0
      | r2_hidden(esk3_0,esk2_0) )
    & ( k4_xboole_0(esk2_0,k1_tarski(esk3_0)) = esk2_0
      | ~ r2_hidden(esk3_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_7,plain,(
    ! [X43] : k2_tarski(X43,X43) = k1_tarski(X43) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_8,plain,(
    ! [X47,X48,X49] :
      ( ( r2_hidden(X47,X48)
        | ~ r2_hidden(X47,k4_xboole_0(X48,k1_tarski(X49))) )
      & ( X47 != X49
        | ~ r2_hidden(X47,k4_xboole_0(X48,k1_tarski(X49))) )
      & ( ~ r2_hidden(X47,X48)
        | X47 = X49
        | r2_hidden(X47,k4_xboole_0(X48,k1_tarski(X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | k4_xboole_0(esk2_0,k1_tarski(esk3_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k4_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_12,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk3_0)) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( k4_xboole_0(esk2_0,k1_tarski(esk3_0)) = esk2_0
    | ~ r2_hidden(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_16,plain,(
    ! [X44,X45,X46] :
      ( ( ~ r2_hidden(X44,X46)
        | k4_xboole_0(k2_tarski(X44,X45),X46) != k1_tarski(X44) )
      & ( r2_hidden(X45,X46)
        | X44 = X45
        | k4_xboole_0(k2_tarski(X44,X45),X46) != k1_tarski(X44) )
      & ( ~ r2_hidden(X45,X46)
        | r2_hidden(X44,X46)
        | k4_xboole_0(k2_tarski(X44,X45),X46) = k1_tarski(X44) )
      & ( X44 != X45
        | r2_hidden(X44,X46)
        | k4_xboole_0(k2_tarski(X44,X45),X46) = k1_tarski(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_zfmisc_1])])])])).

cnf(c_0_17,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k2_tarski(X2,X2))) ),
    inference(rw,[status(thm)],[c_0_12,c_0_10])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,k2_tarski(esk3_0,esk3_0),esk2_0),esk2_0)
    | r2_hidden(esk3_0,esk2_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14])])).

cnf(c_0_20,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk3_0)) = esk2_0
    | ~ r2_hidden(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_15,c_0_10])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X1,X1))) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk3_0)) = esk2_0
    | r2_hidden(esk1_3(esk2_0,k2_tarski(esk3_0,esk3_0),esk2_0),k2_tarski(esk3_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_19]),c_0_20])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X1)
    | r2_hidden(X1,X3)
    | X1 != X2 ),
    inference(rw,[status(thm)],[c_0_21,c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,k2_tarski(esk3_0,esk3_0),esk2_0),k2_tarski(esk3_0,esk3_0))
    | ~ r2_hidden(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k2_tarski(X1,X1),X2) = k2_tarski(X1,X1)
    | r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,k2_tarski(esk3_0,esk3_0),esk2_0),k2_tarski(esk3_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_23]),c_0_26])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k2_tarski(X1,X1))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk3_0)) = esk2_0
    | r2_hidden(esk1_3(esk2_0,k2_tarski(esk3_0,esk3_0),esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | ~ r2_hidden(esk1_3(esk2_0,k2_tarski(esk3_0,esk3_0),esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,k2_tarski(esk3_0,esk3_0),esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_32]),c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk3_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_35])])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_36]),c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:21:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.42  # and selection function SelectNegativeLiterals.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.028 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t65_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.19/0.42  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.42  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.19/0.42  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.42  fof(l38_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)<=>(~(r2_hidden(X1,X3))&(r2_hidden(X2,X3)|X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 0.19/0.42  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1)))), inference(assume_negation,[status(cth)],[t65_zfmisc_1])).
% 0.19/0.42  fof(c_0_6, negated_conjecture, ((k4_xboole_0(esk2_0,k1_tarski(esk3_0))!=esk2_0|r2_hidden(esk3_0,esk2_0))&(k4_xboole_0(esk2_0,k1_tarski(esk3_0))=esk2_0|~r2_hidden(esk3_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).
% 0.19/0.42  fof(c_0_7, plain, ![X43]:k2_tarski(X43,X43)=k1_tarski(X43), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.42  fof(c_0_8, plain, ![X47, X48, X49]:(((r2_hidden(X47,X48)|~r2_hidden(X47,k4_xboole_0(X48,k1_tarski(X49))))&(X47!=X49|~r2_hidden(X47,k4_xboole_0(X48,k1_tarski(X49)))))&(~r2_hidden(X47,X48)|X47=X49|r2_hidden(X47,k4_xboole_0(X48,k1_tarski(X49))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.19/0.42  cnf(c_0_9, negated_conjecture, (r2_hidden(esk3_0,esk2_0)|k4_xboole_0(esk2_0,k1_tarski(esk3_0))!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.42  cnf(c_0_10, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.42  fof(c_0_11, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.42  cnf(c_0_12, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.42  cnf(c_0_13, negated_conjecture, (r2_hidden(esk3_0,esk2_0)|k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk3_0))!=esk2_0), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.19/0.42  cnf(c_0_14, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.42  cnf(c_0_15, negated_conjecture, (k4_xboole_0(esk2_0,k1_tarski(esk3_0))=esk2_0|~r2_hidden(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.42  fof(c_0_16, plain, ![X44, X45, X46]:(((~r2_hidden(X44,X46)|k4_xboole_0(k2_tarski(X44,X45),X46)!=k1_tarski(X44))&(r2_hidden(X45,X46)|X44=X45|k4_xboole_0(k2_tarski(X44,X45),X46)!=k1_tarski(X44)))&((~r2_hidden(X45,X46)|r2_hidden(X44,X46)|k4_xboole_0(k2_tarski(X44,X45),X46)=k1_tarski(X44))&(X44!=X45|r2_hidden(X44,X46)|k4_xboole_0(k2_tarski(X44,X45),X46)=k1_tarski(X44)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_zfmisc_1])])])])).
% 0.19/0.42  cnf(c_0_17, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k2_tarski(X2,X2)))), inference(rw,[status(thm)],[c_0_12, c_0_10])).
% 0.19/0.42  cnf(c_0_18, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.42  cnf(c_0_19, negated_conjecture, (r2_hidden(esk1_3(esk2_0,k2_tarski(esk3_0,esk3_0),esk2_0),esk2_0)|r2_hidden(esk3_0,esk2_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14])])).
% 0.19/0.42  cnf(c_0_20, negated_conjecture, (k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk3_0))=esk2_0|~r2_hidden(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_15, c_0_10])).
% 0.19/0.42  cnf(c_0_21, plain, (r2_hidden(X1,X3)|k4_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.42  cnf(c_0_22, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X1,X1)))), inference(er,[status(thm)],[c_0_17])).
% 0.19/0.42  cnf(c_0_23, negated_conjecture, (k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk3_0))=esk2_0|r2_hidden(esk1_3(esk2_0,k2_tarski(esk3_0,esk3_0),esk2_0),k2_tarski(esk3_0,esk3_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_19]), c_0_20])).
% 0.19/0.42  cnf(c_0_24, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.42  cnf(c_0_25, plain, (k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X1)|r2_hidden(X1,X3)|X1!=X2), inference(rw,[status(thm)],[c_0_21, c_0_10])).
% 0.19/0.42  cnf(c_0_26, negated_conjecture, (r2_hidden(esk1_3(esk2_0,k2_tarski(esk3_0,esk3_0),esk2_0),k2_tarski(esk3_0,esk3_0))|~r2_hidden(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.42  cnf(c_0_27, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_24])).
% 0.19/0.42  cnf(c_0_28, plain, (k4_xboole_0(k2_tarski(X1,X1),X2)=k2_tarski(X1,X1)|r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_25])).
% 0.19/0.42  cnf(c_0_29, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.42  cnf(c_0_30, negated_conjecture, (r2_hidden(esk1_3(esk2_0,k2_tarski(esk3_0,esk3_0),esk2_0),k2_tarski(esk3_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_23]), c_0_26])).
% 0.19/0.42  cnf(c_0_31, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k2_tarski(X1,X1))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.42  cnf(c_0_32, negated_conjecture, (k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk3_0))=esk2_0|r2_hidden(esk1_3(esk2_0,k2_tarski(esk3_0,esk3_0),esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.42  cnf(c_0_33, negated_conjecture, (r2_hidden(esk3_0,X1)|~r2_hidden(esk1_3(esk2_0,k2_tarski(esk3_0,esk3_0),esk2_0),X1)), inference(spm,[status(thm)],[c_0_31, c_0_30])).
% 0.19/0.42  cnf(c_0_34, negated_conjecture, (r2_hidden(esk1_3(esk2_0,k2_tarski(esk3_0,esk3_0),esk2_0),esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_32]), c_0_19])).
% 0.19/0.42  cnf(c_0_35, negated_conjecture, (r2_hidden(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.42  cnf(c_0_36, negated_conjecture, (k4_xboole_0(esk2_0,k2_tarski(esk3_0,esk3_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_35])])).
% 0.19/0.42  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_36]), c_0_35])]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 38
% 0.19/0.42  # Proof object clause steps            : 27
% 0.19/0.42  # Proof object formula steps           : 11
% 0.19/0.42  # Proof object conjectures             : 17
% 0.19/0.42  # Proof object clause conjectures      : 14
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 9
% 0.19/0.42  # Proof object initial formulas used   : 5
% 0.19/0.42  # Proof object generating inferences   : 10
% 0.19/0.42  # Proof object simplifying inferences  : 16
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 16
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 27
% 0.19/0.42  # Removed in clause preprocessing      : 2
% 0.19/0.42  # Initial clauses in saturation        : 25
% 0.19/0.42  # Processed clauses                    : 410
% 0.19/0.42  # ...of these trivial                  : 8
% 0.19/0.42  # ...subsumed                          : 281
% 0.19/0.42  # ...remaining for further processing  : 121
% 0.19/0.42  # Other redundant clauses eliminated   : 19
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 1
% 0.19/0.42  # Backward-rewritten                   : 16
% 0.19/0.42  # Generated clauses                    : 2694
% 0.19/0.42  # ...of the previous two non-trivial   : 2337
% 0.19/0.42  # Contextual simplify-reflections      : 5
% 0.19/0.42  # Paramodulations                      : 2674
% 0.19/0.42  # Factorizations                       : 0
% 0.19/0.42  # Equation resolutions                 : 20
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 76
% 0.19/0.42  #    Positive orientable unit clauses  : 23
% 0.19/0.42  #    Positive unorientable unit clauses: 2
% 0.19/0.42  #    Negative unit clauses             : 8
% 0.19/0.42  #    Non-unit-clauses                  : 43
% 0.19/0.42  # Current number of unprocessed clauses: 1919
% 0.19/0.42  # ...number of literals in the above   : 4359
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 42
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 545
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 478
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 106
% 0.19/0.42  # Unit Clause-clause subsumption calls : 85
% 0.19/0.42  # Rewrite failures with RHS unbound    : 120
% 0.19/0.42  # BW rewrite match attempts            : 281
% 0.19/0.42  # BW rewrite match successes           : 48
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 35357
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.068 s
% 0.19/0.42  # System time              : 0.006 s
% 0.19/0.42  # Total time               : 0.074 s
% 0.19/0.42  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
