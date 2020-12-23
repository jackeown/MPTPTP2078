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
% DateTime   : Thu Dec  3 10:40:40 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   38 (  75 expanded)
%              Number of clauses        :   21 (  35 expanded)
%              Number of leaves         :    8 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  105 ( 145 expanded)
%              Number of equality atoms :   47 (  81 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t47_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X1,X2),X3),X3)
     => r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X1,X2),X3),X3)
       => r2_hidden(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t47_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X31,X32] : k3_tarski(k2_tarski(X31,X32)) = k2_xboole_0(X31,X32) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X29,X30] : k1_enumset1(X29,X29,X30) = k2_tarski(X29,X30) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0),esk5_0)
    & ~ r2_hidden(esk3_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_12,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_15,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X10,X9)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X14)
        | r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k2_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X18,X19] : r1_tarski(X18,k2_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(esk3_0,esk3_0,esk4_0),k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)),esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_13]),c_0_17])).

cnf(c_0_23,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k3_tarski(k1_enumset1(X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_17]),c_0_17])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X23,X22)
        | X23 = X20
        | X23 = X21
        | X22 != k2_tarski(X20,X21) )
      & ( X24 != X20
        | r2_hidden(X24,X22)
        | X22 != k2_tarski(X20,X21) )
      & ( X24 != X21
        | r2_hidden(X24,X22)
        | X22 != k2_tarski(X20,X21) )
      & ( esk2_3(X25,X26,X27) != X25
        | ~ r2_hidden(esk2_3(X25,X26,X27),X27)
        | X27 = k2_tarski(X25,X26) )
      & ( esk2_3(X25,X26,X27) != X26
        | ~ r2_hidden(esk2_3(X25,X26,X27),X27)
        | X27 = k2_tarski(X25,X26) )
      & ( r2_hidden(esk2_3(X25,X26,X27),X27)
        | esk2_3(X25,X26,X27) = X25
        | esk2_3(X25,X26,X27) = X26
        | X27 = k2_tarski(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k1_enumset1(X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_17])).

cnf(c_0_27,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k3_tarski(k1_enumset1(esk5_0,esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0))),esk5_0) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_17])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk5_0,esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0))) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X4) ),
    inference(rw,[status(thm)],[c_0_30,c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_33])])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n016.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 17:46:19 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.11/0.36  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.11/0.36  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.11/0.36  #
% 0.11/0.36  # Preprocessing time       : 0.027 s
% 0.11/0.36  # Presaturation interreduction done
% 0.11/0.36  
% 0.11/0.36  # Proof found!
% 0.11/0.36  # SZS status Theorem
% 0.11/0.36  # SZS output start CNFRefutation
% 0.11/0.36  fof(t47_zfmisc_1, conjecture, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(k2_tarski(X1,X2),X3),X3)=>r2_hidden(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 0.11/0.36  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.11/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.11/0.36  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.11/0.36  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.11/0.36  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.11/0.36  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.11/0.36  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.11/0.36  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(k2_xboole_0(k2_tarski(X1,X2),X3),X3)=>r2_hidden(X1,X3))), inference(assume_negation,[status(cth)],[t47_zfmisc_1])).
% 0.11/0.36  fof(c_0_9, plain, ![X31, X32]:k3_tarski(k2_tarski(X31,X32))=k2_xboole_0(X31,X32), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.11/0.36  fof(c_0_10, plain, ![X29, X30]:k1_enumset1(X29,X29,X30)=k2_tarski(X29,X30), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.11/0.36  fof(c_0_11, negated_conjecture, (r1_tarski(k2_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0),esk5_0)&~r2_hidden(esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.11/0.36  cnf(c_0_12, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.11/0.36  cnf(c_0_13, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.11/0.36  fof(c_0_14, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.11/0.36  fof(c_0_15, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X10,X9)|(r2_hidden(X10,X7)|r2_hidden(X10,X8))|X9!=k2_xboole_0(X7,X8))&((~r2_hidden(X11,X7)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))&(~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))))&(((~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13)))&(r2_hidden(esk1_3(X12,X13,X14),X14)|(r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k2_xboole_0(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.11/0.36  cnf(c_0_16, negated_conjecture, (r1_tarski(k2_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.11/0.36  cnf(c_0_17, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.11/0.36  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.11/0.36  fof(c_0_19, plain, ![X18, X19]:r1_tarski(X18,k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.11/0.36  cnf(c_0_20, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.36  fof(c_0_21, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.11/0.36  cnf(c_0_22, negated_conjecture, (r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(esk3_0,esk3_0,esk4_0),k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)),esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_13]), c_0_17])).
% 0.11/0.36  cnf(c_0_23, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k3_tarski(k1_enumset1(X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_17]), c_0_17])).
% 0.11/0.36  cnf(c_0_24, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.11/0.36  fof(c_0_25, plain, ![X20, X21, X22, X23, X24, X25, X26, X27]:(((~r2_hidden(X23,X22)|(X23=X20|X23=X21)|X22!=k2_tarski(X20,X21))&((X24!=X20|r2_hidden(X24,X22)|X22!=k2_tarski(X20,X21))&(X24!=X21|r2_hidden(X24,X22)|X22!=k2_tarski(X20,X21))))&(((esk2_3(X25,X26,X27)!=X25|~r2_hidden(esk2_3(X25,X26,X27),X27)|X27=k2_tarski(X25,X26))&(esk2_3(X25,X26,X27)!=X26|~r2_hidden(esk2_3(X25,X26,X27),X27)|X27=k2_tarski(X25,X26)))&(r2_hidden(esk2_3(X25,X26,X27),X27)|(esk2_3(X25,X26,X27)=X25|esk2_3(X25,X26,X27)=X26)|X27=k2_tarski(X25,X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.11/0.36  cnf(c_0_26, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k1_enumset1(X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_17])).
% 0.11/0.36  cnf(c_0_27, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.11/0.36  cnf(c_0_28, negated_conjecture, (r1_tarski(k3_tarski(k1_enumset1(esk5_0,esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0))),esk5_0)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.11/0.36  cnf(c_0_29, plain, (r1_tarski(X1,k3_tarski(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_24, c_0_17])).
% 0.11/0.36  cnf(c_0_30, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.11/0.36  cnf(c_0_31, plain, (r2_hidden(X1,k3_tarski(k1_enumset1(X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_26])).
% 0.11/0.36  cnf(c_0_32, negated_conjecture, (k3_tarski(k1_enumset1(esk5_0,esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0)))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.11/0.36  cnf(c_0_33, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X4)), inference(rw,[status(thm)],[c_0_30, c_0_13])).
% 0.11/0.36  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k1_enumset1(esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.11/0.36  cnf(c_0_35, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_33])])).
% 0.11/0.36  cnf(c_0_36, negated_conjecture, (~r2_hidden(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.11/0.36  cnf(c_0_37, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), ['proof']).
% 0.11/0.36  # SZS output end CNFRefutation
% 0.11/0.36  # Proof object total steps             : 38
% 0.11/0.36  # Proof object clause steps            : 21
% 0.11/0.36  # Proof object formula steps           : 17
% 0.11/0.36  # Proof object conjectures             : 10
% 0.11/0.36  # Proof object clause conjectures      : 7
% 0.11/0.36  # Proof object formula conjectures     : 3
% 0.11/0.36  # Proof object initial clauses used    : 9
% 0.11/0.36  # Proof object initial formulas used   : 8
% 0.11/0.36  # Proof object generating inferences   : 3
% 0.11/0.36  # Proof object simplifying inferences  : 15
% 0.11/0.36  # Training examples: 0 positive, 0 negative
% 0.11/0.36  # Parsed axioms                        : 8
% 0.11/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.36  # Initial clauses                      : 21
% 0.11/0.36  # Removed in clause preprocessing      : 2
% 0.11/0.36  # Initial clauses in saturation        : 19
% 0.11/0.36  # Processed clauses                    : 50
% 0.11/0.36  # ...of these trivial                  : 1
% 0.11/0.36  # ...subsumed                          : 0
% 0.11/0.36  # ...remaining for further processing  : 49
% 0.11/0.36  # Other redundant clauses eliminated   : 10
% 0.11/0.36  # Clauses deleted for lack of memory   : 0
% 0.11/0.36  # Backward-subsumed                    : 0
% 0.11/0.36  # Backward-rewritten                   : 2
% 0.11/0.36  # Generated clauses                    : 61
% 0.11/0.36  # ...of the previous two non-trivial   : 50
% 0.11/0.36  # Contextual simplify-reflections      : 0
% 0.11/0.36  # Paramodulations                      : 47
% 0.11/0.36  # Factorizations                       : 6
% 0.11/0.36  # Equation resolutions                 : 10
% 0.11/0.36  # Propositional unsat checks           : 0
% 0.11/0.36  #    Propositional check models        : 0
% 0.11/0.36  #    Propositional check unsatisfiable : 0
% 0.11/0.36  #    Propositional clauses             : 0
% 0.11/0.36  #    Propositional clauses after purity: 0
% 0.11/0.36  #    Propositional unsat core size     : 0
% 0.11/0.36  #    Propositional preprocessing time  : 0.000
% 0.11/0.36  #    Propositional encoding time       : 0.000
% 0.11/0.36  #    Propositional solver time         : 0.000
% 0.11/0.36  #    Success case prop preproc time    : 0.000
% 0.11/0.36  #    Success case prop encoding time   : 0.000
% 0.11/0.36  #    Success case prop solver time     : 0.000
% 0.11/0.36  # Current number of processed clauses  : 21
% 0.11/0.36  #    Positive orientable unit clauses  : 7
% 0.11/0.36  #    Positive unorientable unit clauses: 1
% 0.11/0.36  #    Negative unit clauses             : 1
% 0.11/0.36  #    Non-unit-clauses                  : 12
% 0.11/0.36  # Current number of unprocessed clauses: 32
% 0.11/0.36  # ...number of literals in the above   : 103
% 0.11/0.36  # Current number of archived formulas  : 0
% 0.11/0.36  # Current number of archived clauses   : 22
% 0.11/0.36  # Clause-clause subsumption calls (NU) : 28
% 0.11/0.36  # Rec. Clause-clause subsumption calls : 22
% 0.11/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.11/0.36  # Unit Clause-clause subsumption calls : 4
% 0.11/0.36  # Rewrite failures with RHS unbound    : 0
% 0.11/0.36  # BW rewrite match attempts            : 15
% 0.11/0.36  # BW rewrite match successes           : 9
% 0.11/0.36  # Condensation attempts                : 0
% 0.11/0.36  # Condensation successes               : 0
% 0.11/0.36  # Termbank termtop insertions          : 2024
% 0.11/0.36  
% 0.11/0.36  # -------------------------------------------------
% 0.11/0.36  # User time                : 0.028 s
% 0.11/0.36  # System time              : 0.005 s
% 0.11/0.36  # Total time               : 0.033 s
% 0.11/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
