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
% DateTime   : Thu Dec  3 10:38:00 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 214 expanded)
%              Number of clauses        :   28 (  87 expanded)
%              Number of leaves         :   10 (  62 expanded)
%              Depth                    :    7
%              Number of atoms          :   97 ( 381 expanded)
%              Number of equality atoms :   45 ( 225 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t19_zfmisc_1,conjecture,(
    ! [X1,X2] : k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t12_zfmisc_1,axiom,(
    ! [X1,X2] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] : k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_tarski(X1) ),
    inference(assume_negation,[status(cth)],[t19_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X20,X21] :
      ( ( r1_tarski(X20,X21)
        | X20 != X21 )
      & ( r1_tarski(X21,X20)
        | X20 != X21 )
      & ( ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X21,X20)
        | X20 = X21 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_12,negated_conjecture,(
    k3_xboole_0(k1_tarski(esk3_0),k2_tarski(esk3_0,esk4_0)) != k1_tarski(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X28] : k2_tarski(X28,X28) = k1_tarski(X28) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,plain,(
    ! [X29,X30] : k1_enumset1(X29,X29,X30) = k2_tarski(X29,X30) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X31,X32,X33] : k2_enumset1(X31,X31,X32,X33) = k1_enumset1(X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_16,plain,(
    ! [X26,X27] : k4_xboole_0(X26,k4_xboole_0(X26,X27)) = k3_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_17,plain,(
    ! [X34,X35] : r1_tarski(k1_tarski(X34),k2_tarski(X34,X35)) ),
    inference(variable_rename,[status(thm)],[t12_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k3_xboole_0(X24,X25)) = k4_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_19,plain,(
    ! [X22,X23] :
      ( ( k4_xboole_0(X22,X23) != k1_xboole_0
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(X22,X23)
        | k4_xboole_0(X22,X23) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_21,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k4_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_22,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk3_0),k2_tarski(esk3_0,esk4_0)) != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))) != k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_23]),c_0_24]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_26])).

cnf(c_0_33,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_23]),c_0_24]),c_0_24]),c_0_25]),c_0_25])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_26])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk2_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33])])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_34])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_37])).

cnf(c_0_44,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk2_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k1_xboole_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k1_xboole_0) != k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_40])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_45])]),c_0_46]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:12:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.40  # and selection function SelectNegativeLiterals.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.048 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t19_zfmisc_1, conjecture, ![X1, X2]:k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 0.19/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.40  fof(t12_zfmisc_1, axiom, ![X1, X2]:r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 0.19/0.40  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.19/0.40  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.40  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.40  fof(c_0_10, negated_conjecture, ~(![X1, X2]:k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_tarski(X1)), inference(assume_negation,[status(cth)],[t19_zfmisc_1])).
% 0.19/0.40  fof(c_0_11, plain, ![X20, X21]:(((r1_tarski(X20,X21)|X20!=X21)&(r1_tarski(X21,X20)|X20!=X21))&(~r1_tarski(X20,X21)|~r1_tarski(X21,X20)|X20=X21)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.40  fof(c_0_12, negated_conjecture, k3_xboole_0(k1_tarski(esk3_0),k2_tarski(esk3_0,esk4_0))!=k1_tarski(esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.19/0.40  fof(c_0_13, plain, ![X28]:k2_tarski(X28,X28)=k1_tarski(X28), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.40  fof(c_0_14, plain, ![X29, X30]:k1_enumset1(X29,X29,X30)=k2_tarski(X29,X30), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.40  fof(c_0_15, plain, ![X31, X32, X33]:k2_enumset1(X31,X31,X32,X33)=k1_enumset1(X31,X32,X33), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.40  fof(c_0_16, plain, ![X26, X27]:k4_xboole_0(X26,k4_xboole_0(X26,X27))=k3_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.40  fof(c_0_17, plain, ![X34, X35]:r1_tarski(k1_tarski(X34),k2_tarski(X34,X35)), inference(variable_rename,[status(thm)],[t12_zfmisc_1])).
% 0.19/0.40  fof(c_0_18, plain, ![X24, X25]:k4_xboole_0(X24,k3_xboole_0(X24,X25))=k4_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.19/0.40  fof(c_0_19, plain, ![X22, X23]:((k4_xboole_0(X22,X23)!=k1_xboole_0|r1_tarski(X22,X23))&(~r1_tarski(X22,X23)|k4_xboole_0(X22,X23)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.40  cnf(c_0_20, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  fof(c_0_21, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.40  cnf(c_0_22, negated_conjecture, (k3_xboole_0(k1_tarski(esk3_0),k2_tarski(esk3_0,esk4_0))!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_23, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_27, plain, (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_28, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_29, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_30, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_31, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.40  cnf(c_0_32, negated_conjecture, (k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)))!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_23]), c_0_24]), c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_26])).
% 0.19/0.40  cnf(c_0_33, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.40  cnf(c_0_34, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_23]), c_0_24]), c_0_24]), c_0_25]), c_0_25])).
% 0.19/0.40  cnf(c_0_35, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.40  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_26])).
% 0.19/0.40  cnf(c_0_37, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.40  cnf(c_0_38, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_31])).
% 0.19/0.40  cnf(c_0_39, negated_conjecture, (r2_hidden(esk2_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33])])).
% 0.19/0.40  cnf(c_0_40, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_34])).
% 0.19/0.40  cnf(c_0_41, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_35])).
% 0.19/0.40  cnf(c_0_42, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.40  cnf(c_0_43, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_38, c_0_37])).
% 0.19/0.40  cnf(c_0_44, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~r2_hidden(esk2_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.40  cnf(c_0_45, negated_conjecture, (r2_hidden(esk2_3(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k1_xboole_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.40  cnf(c_0_46, negated_conjecture, (k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k1_xboole_0)!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_32, c_0_40])).
% 0.19/0.40  cnf(c_0_47, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.19/0.40  cnf(c_0_48, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_45])]), c_0_46]), c_0_47]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 49
% 0.19/0.40  # Proof object clause steps            : 28
% 0.19/0.40  # Proof object formula steps           : 21
% 0.19/0.40  # Proof object conjectures             : 9
% 0.19/0.40  # Proof object clause conjectures      : 6
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 13
% 0.19/0.40  # Proof object initial formulas used   : 10
% 0.19/0.40  # Proof object generating inferences   : 7
% 0.19/0.40  # Proof object simplifying inferences  : 26
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 11
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 21
% 0.19/0.40  # Removed in clause preprocessing      : 4
% 0.19/0.40  # Initial clauses in saturation        : 17
% 0.19/0.40  # Processed clauses                    : 72
% 0.19/0.40  # ...of these trivial                  : 0
% 0.19/0.40  # ...subsumed                          : 14
% 0.19/0.40  # ...remaining for further processing  : 58
% 0.19/0.40  # Other redundant clauses eliminated   : 11
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 0
% 0.19/0.40  # Backward-rewritten                   : 4
% 0.19/0.40  # Generated clauses                    : 159
% 0.19/0.40  # ...of the previous two non-trivial   : 133
% 0.19/0.40  # Contextual simplify-reflections      : 1
% 0.19/0.40  # Paramodulations                      : 148
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 11
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 33
% 0.19/0.40  #    Positive orientable unit clauses  : 8
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 2
% 0.19/0.40  #    Non-unit-clauses                  : 23
% 0.19/0.40  # Current number of unprocessed clauses: 91
% 0.19/0.40  # ...number of literals in the above   : 273
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 24
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 56
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 35
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 10
% 0.19/0.40  # Unit Clause-clause subsumption calls : 5
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 5
% 0.19/0.40  # BW rewrite match successes           : 1
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 3396
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.055 s
% 0.19/0.40  # System time              : 0.004 s
% 0.19/0.40  # Total time               : 0.059 s
% 0.19/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
