%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:21 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 105 expanded)
%              Number of clauses        :   24 (  43 expanded)
%              Number of leaves         :   13 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   99 ( 154 expanded)
%              Number of equality atoms :   58 ( 113 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_zfmisc_1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(fc5_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X1)
     => ~ v1_xboole_0(k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t50_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X39,X40] : k3_tarski(k2_tarski(X39,X40)) = k2_xboole_0(X39,X40) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X30,X31] : k1_enumset1(X30,X30,X31) = k2_tarski(X30,X31) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_17,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X32,X33,X34] : k2_enumset1(X32,X32,X33,X34) = k1_enumset1(X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X35,X36,X37,X38] : k3_enumset1(X35,X35,X36,X37,X38) = k2_enumset1(X35,X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_21,plain,(
    ! [X17,X18] : k2_tarski(X17,X18) = k2_tarski(X18,X17) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_22,plain,(
    ! [X13,X14] :
      ( v1_xboole_0(X13)
      | ~ v1_xboole_0(k2_xboole_0(X14,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_xboole_0])])])).

cnf(c_0_23,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X19,X20,X21,X22,X23,X24,X25,X26,X27,X28] :
      ( ( ~ r2_hidden(X23,X22)
        | X23 = X19
        | X23 = X20
        | X23 = X21
        | X22 != k1_enumset1(X19,X20,X21) )
      & ( X24 != X19
        | r2_hidden(X24,X22)
        | X22 != k1_enumset1(X19,X20,X21) )
      & ( X24 != X20
        | r2_hidden(X24,X22)
        | X22 != k1_enumset1(X19,X20,X21) )
      & ( X24 != X21
        | r2_hidden(X24,X22)
        | X22 != k1_enumset1(X19,X20,X21) )
      & ( esk2_4(X25,X26,X27,X28) != X25
        | ~ r2_hidden(esk2_4(X25,X26,X27,X28),X28)
        | X28 = k1_enumset1(X25,X26,X27) )
      & ( esk2_4(X25,X26,X27,X28) != X26
        | ~ r2_hidden(esk2_4(X25,X26,X27,X28),X28)
        | X28 = k1_enumset1(X25,X26,X27) )
      & ( esk2_4(X25,X26,X27,X28) != X27
        | ~ r2_hidden(esk2_4(X25,X26,X27,X28),X28)
        | X28 = k1_enumset1(X25,X26,X27) )
      & ( r2_hidden(esk2_4(X25,X26,X27,X28),X28)
        | esk2_4(X25,X26,X27,X28) = X25
        | esk2_4(X25,X26,X27,X28) = X26
        | esk2_4(X25,X26,X27,X28) = X27
        | X28 = k1_enumset1(X25,X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_29,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(k2_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_18]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_18]),c_0_18]),c_0_25]),c_0_25]),c_0_26]),c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_33,plain,(
    ! [X6] :
      ( ~ v1_xboole_0(X6)
      | X6 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_37,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r1_xboole_0(X7,X8)
        | r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)) )
      & ( ~ r2_hidden(X12,k3_xboole_0(X10,X11))
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_38,plain,(
    ! [X16] : r1_xboole_0(X16,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_39,plain,(
    ! [X15] : k3_xboole_0(X15,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_25]),c_0_26])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( v1_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).

cnf(c_0_47,negated_conjecture,
    ( k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:25:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.38  # and selection function SelectNegativeLiterals.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.027 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t50_zfmisc_1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 0.19/0.38  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.38  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.38  fof(fc5_xboole_0, axiom, ![X1, X2]:(~(v1_xboole_0(X1))=>~(v1_xboole_0(k2_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_xboole_0)).
% 0.19/0.38  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.19/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.19/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.38  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.38  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.38  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.19/0.38  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0), inference(assume_negation,[status(cth)],[t50_zfmisc_1])).
% 0.19/0.38  fof(c_0_14, plain, ![X39, X40]:k3_tarski(k2_tarski(X39,X40))=k2_xboole_0(X39,X40), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.38  fof(c_0_15, plain, ![X30, X31]:k1_enumset1(X30,X30,X31)=k2_tarski(X30,X31), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.38  fof(c_0_16, negated_conjecture, k2_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.19/0.38  cnf(c_0_17, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  fof(c_0_19, plain, ![X32, X33, X34]:k2_enumset1(X32,X32,X33,X34)=k1_enumset1(X32,X33,X34), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.38  fof(c_0_20, plain, ![X35, X36, X37, X38]:k3_enumset1(X35,X35,X36,X37,X38)=k2_enumset1(X35,X36,X37,X38), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.38  fof(c_0_21, plain, ![X17, X18]:k2_tarski(X17,X18)=k2_tarski(X18,X17), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.38  fof(c_0_22, plain, ![X13, X14]:(v1_xboole_0(X13)|~v1_xboole_0(k2_xboole_0(X14,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_xboole_0])])])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (k2_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_24, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.38  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_26, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_27, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  fof(c_0_28, plain, ![X19, X20, X21, X22, X23, X24, X25, X26, X27, X28]:(((~r2_hidden(X23,X22)|(X23=X19|X23=X20|X23=X21)|X22!=k1_enumset1(X19,X20,X21))&(((X24!=X19|r2_hidden(X24,X22)|X22!=k1_enumset1(X19,X20,X21))&(X24!=X20|r2_hidden(X24,X22)|X22!=k1_enumset1(X19,X20,X21)))&(X24!=X21|r2_hidden(X24,X22)|X22!=k1_enumset1(X19,X20,X21))))&((((esk2_4(X25,X26,X27,X28)!=X25|~r2_hidden(esk2_4(X25,X26,X27,X28),X28)|X28=k1_enumset1(X25,X26,X27))&(esk2_4(X25,X26,X27,X28)!=X26|~r2_hidden(esk2_4(X25,X26,X27,X28),X28)|X28=k1_enumset1(X25,X26,X27)))&(esk2_4(X25,X26,X27,X28)!=X27|~r2_hidden(esk2_4(X25,X26,X27,X28),X28)|X28=k1_enumset1(X25,X26,X27)))&(r2_hidden(esk2_4(X25,X26,X27,X28),X28)|(esk2_4(X25,X26,X27,X28)=X25|esk2_4(X25,X26,X27,X28)=X26|esk2_4(X25,X26,X27,X28)=X27)|X28=k1_enumset1(X25,X26,X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.19/0.38  cnf(c_0_29, plain, (v1_xboole_0(X1)|~v1_xboole_0(k2_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (k3_tarski(k3_enumset1(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_18]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 0.19/0.38  cnf(c_0_31, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_18]), c_0_18]), c_0_25]), c_0_25]), c_0_26]), c_0_26])).
% 0.19/0.38  cnf(c_0_32, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.38  fof(c_0_33, plain, ![X6]:(~v1_xboole_0(X6)|X6=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.19/0.38  cnf(c_0_34, plain, (v1_xboole_0(X1)|~v1_xboole_0(k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_24]), c_0_25]), c_0_26])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.38  cnf(c_0_36, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.38  fof(c_0_37, plain, ![X7, X8, X10, X11, X12]:((r1_xboole_0(X7,X8)|r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)))&(~r2_hidden(X12,k3_xboole_0(X10,X11))|~r1_xboole_0(X10,X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.38  fof(c_0_38, plain, ![X16]:r1_xboole_0(X16,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.38  fof(c_0_39, plain, ![X15]:k3_xboole_0(X15,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.19/0.38  cnf(c_0_40, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_25]), c_0_26])).
% 0.19/0.38  cnf(c_0_41, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (v1_xboole_0(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.19/0.38  cnf(c_0_43, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.38  cnf(c_0_44, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_45, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.38  cnf(c_0_46, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.38  cnf(c_0_48, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 50
% 0.19/0.38  # Proof object clause steps            : 24
% 0.19/0.38  # Proof object formula steps           : 26
% 0.19/0.38  # Proof object conjectures             : 9
% 0.19/0.38  # Proof object clause conjectures      : 6
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 13
% 0.19/0.38  # Proof object initial formulas used   : 13
% 0.19/0.38  # Proof object generating inferences   : 4
% 0.19/0.38  # Proof object simplifying inferences  : 28
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 13
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 21
% 0.19/0.38  # Removed in clause preprocessing      : 4
% 0.19/0.38  # Initial clauses in saturation        : 17
% 0.19/0.38  # Processed clauses                    : 36
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 0
% 0.19/0.38  # ...remaining for further processing  : 36
% 0.19/0.38  # Other redundant clauses eliminated   : 7
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 3
% 0.19/0.38  # Generated clauses                    : 12
% 0.19/0.38  # ...of the previous two non-trivial   : 11
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 8
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 7
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 12
% 0.19/0.38  #    Positive orientable unit clauses  : 7
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 4
% 0.19/0.38  # Current number of unprocessed clauses: 7
% 0.19/0.38  # ...number of literals in the above   : 21
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 24
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 6
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 6
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.38  # Unit Clause-clause subsumption calls : 1
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 19
% 0.19/0.38  # BW rewrite match successes           : 7
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 1291
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.028 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.032 s
% 0.19/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
