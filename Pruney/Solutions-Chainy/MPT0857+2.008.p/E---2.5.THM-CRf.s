%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:04 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 175 expanded)
%              Number of clauses        :   31 (  77 expanded)
%              Number of leaves         :    8 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  119 ( 388 expanded)
%              Number of equality atoms :   36 ( 154 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,k1_tarski(X3)))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & k2_mcart_1(X1) = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k2_zfmisc_1(X2,k1_tarski(X3)))
       => ( r2_hidden(k1_mcart_1(X1),X2)
          & k2_mcart_1(X1) = X3 ) ) ),
    inference(assume_negation,[status(cth)],[t13_mcart_1])).

fof(c_0_9,plain,(
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

fof(c_0_10,plain,(
    ! [X23,X24] :
      ( ( k4_xboole_0(X23,k1_tarski(X24)) != X23
        | ~ r2_hidden(X24,X23) )
      & ( r2_hidden(X24,X23)
        | k4_xboole_0(X23,k1_tarski(X24)) = X23 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_11,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))
    & ( ~ r2_hidden(k1_mcart_1(esk2_0),esk3_0)
      | k2_mcart_1(esk2_0) != esk4_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X25,X26,X27] :
      ( ( r2_hidden(k1_mcart_1(X25),X26)
        | ~ r2_hidden(X25,k2_zfmisc_1(X26,X27)) )
      & ( r2_hidden(k2_mcart_1(X25),X27)
        | ~ r2_hidden(X25,k2_zfmisc_1(X26,X27)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_27,plain,(
    ! [X20,X21,X22] :
      ( ( r2_hidden(X20,X21)
        | ~ r2_hidden(X20,k4_xboole_0(X21,k1_tarski(X22))) )
      & ( X20 != X22
        | ~ r2_hidden(X20,k4_xboole_0(X21,k1_tarski(X22))) )
      & ( ~ r2_hidden(X20,X21)
        | X20 = X22
        | r2_hidden(X20,k4_xboole_0(X21,k1_tarski(X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k2_enumset1(X1,X1,X1,X1))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk4_0,X1)
    | ~ r2_hidden(k2_mcart_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),X1))
    | r2_hidden(k2_mcart_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_34,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk4_0,k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),X1))
    | r2_hidden(k2_mcart_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),X1)
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_35])).

cnf(c_0_40,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk4_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(k1_mcart_1(esk2_0),esk3_0)
    | k2_mcart_1(esk2_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_25])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k4_xboole_0(X1,k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( esk4_0 = X1
    | r2_hidden(esk4_0,k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k2_enumset1(X1,X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( k2_mcart_1(esk2_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n016.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 11:42:34 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S0U
% 0.12/0.36  # and selection function SelectComplexExceptRRHorn.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.027 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t13_mcart_1, conjecture, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,k1_tarski(X3)))=>(r2_hidden(k1_mcart_1(X1),X2)&k2_mcart_1(X1)=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_mcart_1)).
% 0.12/0.36  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.12/0.36  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.12/0.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.36  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.36  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.12/0.36  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.12/0.36  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,k1_tarski(X3)))=>(r2_hidden(k1_mcart_1(X1),X2)&k2_mcart_1(X1)=X3))), inference(assume_negation,[status(cth)],[t13_mcart_1])).
% 0.12/0.36  fof(c_0_9, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.12/0.36  fof(c_0_10, plain, ![X23, X24]:((k4_xboole_0(X23,k1_tarski(X24))!=X23|~r2_hidden(X24,X23))&(r2_hidden(X24,X23)|k4_xboole_0(X23,k1_tarski(X24))=X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.12/0.36  fof(c_0_11, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.36  fof(c_0_12, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.36  fof(c_0_13, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.36  fof(c_0_14, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))&(~r2_hidden(k1_mcart_1(esk2_0),esk3_0)|k2_mcart_1(esk2_0)!=esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.12/0.36  cnf(c_0_15, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.36  cnf(c_0_16, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.36  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.36  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.36  cnf(c_0_19, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.36  fof(c_0_20, plain, ![X25, X26, X27]:((r2_hidden(k1_mcart_1(X25),X26)|~r2_hidden(X25,k2_zfmisc_1(X26,X27)))&(r2_hidden(k2_mcart_1(X25),X27)|~r2_hidden(X25,k2_zfmisc_1(X26,X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.12/0.36  cnf(c_0_21, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.36  cnf(c_0_22, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_15])).
% 0.12/0.36  cnf(c_0_23, plain, (k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19])).
% 0.12/0.36  cnf(c_0_24, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.36  cnf(c_0_25, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_17]), c_0_18]), c_0_19])).
% 0.12/0.36  cnf(c_0_26, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.36  fof(c_0_27, plain, ![X20, X21, X22]:(((r2_hidden(X20,X21)|~r2_hidden(X20,k4_xboole_0(X21,k1_tarski(X22))))&(X20!=X22|~r2_hidden(X20,k4_xboole_0(X21,k1_tarski(X22)))))&(~r2_hidden(X20,X21)|X20=X22|r2_hidden(X20,k4_xboole_0(X21,k1_tarski(X22))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.12/0.36  cnf(c_0_28, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k2_enumset1(X1,X1,X1,X1))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.12/0.36  cnf(c_0_29, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.12/0.36  cnf(c_0_30, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_26])).
% 0.12/0.36  cnf(c_0_31, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.36  cnf(c_0_32, negated_conjecture, (r2_hidden(esk4_0,X1)|~r2_hidden(k2_mcart_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.12/0.36  cnf(c_0_33, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),X1))|r2_hidden(k2_mcart_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_30, c_0_29])).
% 0.12/0.36  cnf(c_0_34, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_17]), c_0_18]), c_0_19])).
% 0.12/0.36  cnf(c_0_35, negated_conjecture, (r2_hidden(esk4_0,k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),X1))|r2_hidden(k2_mcart_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.12/0.36  cnf(c_0_36, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.36  cnf(c_0_37, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.36  cnf(c_0_38, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))), inference(er,[status(thm)],[c_0_34])).
% 0.12/0.36  cnf(c_0_39, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),X1)|~r2_hidden(esk4_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_35])).
% 0.12/0.36  cnf(c_0_40, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_17]), c_0_18]), c_0_19])).
% 0.12/0.36  cnf(c_0_41, negated_conjecture, (r2_hidden(esk4_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_32, c_0_29])).
% 0.12/0.36  cnf(c_0_42, negated_conjecture, (~r2_hidden(k1_mcart_1(esk2_0),esk3_0)|k2_mcart_1(esk2_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.36  cnf(c_0_43, negated_conjecture, (r2_hidden(k1_mcart_1(esk2_0),esk3_0)), inference(spm,[status(thm)],[c_0_37, c_0_25])).
% 0.12/0.36  cnf(c_0_44, negated_conjecture, (~r2_hidden(esk4_0,k4_xboole_0(X1,k2_enumset1(k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0),k2_mcart_1(esk2_0))))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.12/0.36  cnf(c_0_45, negated_conjecture, (esk4_0=X1|r2_hidden(esk4_0,k4_xboole_0(k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0),k2_enumset1(X1,X1,X1,X1)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.12/0.36  cnf(c_0_46, negated_conjecture, (k2_mcart_1(esk2_0)!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43])])).
% 0.12/0.36  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 48
% 0.12/0.36  # Proof object clause steps            : 31
% 0.12/0.36  # Proof object formula steps           : 17
% 0.12/0.36  # Proof object conjectures             : 17
% 0.12/0.36  # Proof object clause conjectures      : 14
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 12
% 0.12/0.36  # Proof object initial formulas used   : 8
% 0.12/0.36  # Proof object generating inferences   : 11
% 0.12/0.36  # Proof object simplifying inferences  : 18
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 8
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 18
% 0.12/0.36  # Removed in clause preprocessing      : 3
% 0.12/0.36  # Initial clauses in saturation        : 15
% 0.12/0.36  # Processed clauses                    : 94
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 23
% 0.12/0.36  # ...remaining for further processing  : 71
% 0.12/0.36  # Other redundant clauses eliminated   : 4
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 1
% 0.12/0.36  # Generated clauses                    : 216
% 0.12/0.36  # ...of the previous two non-trivial   : 149
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 210
% 0.12/0.36  # Factorizations                       : 2
% 0.12/0.36  # Equation resolutions                 : 4
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 52
% 0.12/0.36  #    Positive orientable unit clauses  : 8
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 3
% 0.12/0.36  #    Non-unit-clauses                  : 41
% 0.12/0.36  # Current number of unprocessed clauses: 79
% 0.12/0.36  # ...number of literals in the above   : 241
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 18
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 202
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 171
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 23
% 0.12/0.36  # Unit Clause-clause subsumption calls : 1
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 1
% 0.12/0.36  # BW rewrite match successes           : 1
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 4126
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.033 s
% 0.12/0.36  # System time              : 0.003 s
% 0.12/0.36  # Total time               : 0.036 s
% 0.12/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
