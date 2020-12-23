%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:19 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 135 expanded)
%              Number of clauses        :   34 (  61 expanded)
%              Number of leaves         :   13 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  100 ( 183 expanded)
%              Number of equality atoms :   34 ( 103 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t76_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(c_0_13,plain,(
    ! [X18] : k3_xboole_0(X18,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_14,plain,(
    ! [X22,X23] : k4_xboole_0(X22,k4_xboole_0(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_15,plain,(
    ! [X16,X17] : k2_xboole_0(X16,k3_xboole_0(X16,X17)) = X16 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_16,plain,(
    ! [X20,X21] : k4_xboole_0(X20,k3_xboole_0(X20,X21)) = k4_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_17,plain,(
    ! [X24,X25,X26] : k4_xboole_0(X24,k4_xboole_0(X25,X26)) = k2_xboole_0(k4_xboole_0(X24,X25),k3_xboole_0(X24,X26)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X19] : k4_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r1_xboole_0(X10,X11)
        | r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)) )
      & ( ~ r2_hidden(X15,k3_xboole_0(X13,X14))
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_24,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_21,c_0_19])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_19])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X27] : r1_xboole_0(X27,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_33,plain,(
    ! [X28,X29,X30] :
      ( ( r1_xboole_0(X28,k2_xboole_0(X29,X30))
        | ~ r1_xboole_0(X28,X29)
        | ~ r1_xboole_0(X28,X30) )
      & ( r1_xboole_0(X28,X29)
        | ~ r1_xboole_0(X28,k2_xboole_0(X29,X30)) )
      & ( r1_xboole_0(X28,X30)
        | ~ r1_xboole_0(X28,k2_xboole_0(X29,X30)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_19])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_19])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_42,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_xboole_0(X1,X2)
       => r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2)) ) ),
    inference(assume_negation,[status(cth)],[t76_xboole_1])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_34,c_0_19])).

fof(c_0_45,plain,(
    ! [X8,X9] :
      ( ~ r1_xboole_0(X8,X9)
      | r1_xboole_0(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_19])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_27]),c_0_38]),c_0_39])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_27]),c_0_37]),c_0_41])])).

fof(c_0_49,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0)
    & ~ r1_xboole_0(k3_xboole_0(esk4_0,esk2_0),k3_xboole_0(esk4_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).

cnf(c_0_50,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X4,X3))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_36])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_44]),c_0_27])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_37]),c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_xboole_0(k3_xboole_0(esk4_0,esk2_0),k3_xboole_0(esk4_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,X4))
    | ~ r1_xboole_0(X4,X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk2_0)),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_19]),c_0_19])).

cnf(c_0_58,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(X2,k4_xboole_0(X2,X4)))
    | ~ r1_xboole_0(X3,X4) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.47/0.68  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.47/0.68  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.47/0.68  #
% 0.47/0.68  # Preprocessing time       : 0.027 s
% 0.47/0.68  # Presaturation interreduction done
% 0.47/0.68  
% 0.47/0.68  # Proof found!
% 0.47/0.68  # SZS status Theorem
% 0.47/0.68  # SZS output start CNFRefutation
% 0.47/0.68  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.47/0.68  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.47/0.68  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.47/0.68  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.47/0.68  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.47/0.68  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.47/0.68  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.47/0.68  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.47/0.68  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.47/0.68  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.47/0.68  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.47/0.68  fof(t76_xboole_1, conjecture, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_xboole_1)).
% 0.47/0.68  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.47/0.68  fof(c_0_13, plain, ![X18]:k3_xboole_0(X18,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.47/0.68  fof(c_0_14, plain, ![X22, X23]:k4_xboole_0(X22,k4_xboole_0(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.47/0.68  fof(c_0_15, plain, ![X16, X17]:k2_xboole_0(X16,k3_xboole_0(X16,X17))=X16, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.47/0.68  fof(c_0_16, plain, ![X20, X21]:k4_xboole_0(X20,k3_xboole_0(X20,X21))=k4_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.47/0.68  fof(c_0_17, plain, ![X24, X25, X26]:k4_xboole_0(X24,k4_xboole_0(X25,X26))=k2_xboole_0(k4_xboole_0(X24,X25),k3_xboole_0(X24,X26)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 0.47/0.68  cnf(c_0_18, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.68  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.47/0.68  fof(c_0_20, plain, ![X19]:k4_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.47/0.68  cnf(c_0_21, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.47/0.68  cnf(c_0_22, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.47/0.68  fof(c_0_23, plain, ![X10, X11, X13, X14, X15]:((r1_xboole_0(X10,X11)|r2_hidden(esk1_2(X10,X11),k3_xboole_0(X10,X11)))&(~r2_hidden(X15,k3_xboole_0(X13,X14))|~r1_xboole_0(X13,X14))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.47/0.68  fof(c_0_24, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.47/0.68  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.68  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.47/0.68  cnf(c_0_27, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.68  fof(c_0_28, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.47/0.68  cnf(c_0_29, plain, (k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_21, c_0_19])).
% 0.47/0.68  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_19])).
% 0.47/0.68  cnf(c_0_31, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.47/0.68  fof(c_0_32, plain, ![X27]:r1_xboole_0(X27,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.47/0.68  fof(c_0_33, plain, ![X28, X29, X30]:((r1_xboole_0(X28,k2_xboole_0(X29,X30))|~r1_xboole_0(X28,X29)|~r1_xboole_0(X28,X30))&((r1_xboole_0(X28,X29)|~r1_xboole_0(X28,k2_xboole_0(X29,X30)))&(r1_xboole_0(X28,X30)|~r1_xboole_0(X28,k2_xboole_0(X29,X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.47/0.68  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.47/0.68  cnf(c_0_35, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.47/0.68  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[c_0_25, c_0_19])).
% 0.47/0.68  cnf(c_0_37, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.47/0.68  cnf(c_0_38, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.47/0.68  cnf(c_0_39, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.47/0.68  cnf(c_0_40, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_31, c_0_19])).
% 0.47/0.68  cnf(c_0_41, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.47/0.68  fof(c_0_42, negated_conjecture, ~(![X1, X2, X3]:(r1_xboole_0(X1,X2)=>r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2)))), inference(assume_negation,[status(cth)],[t76_xboole_1])).
% 0.47/0.68  cnf(c_0_43, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.47/0.68  cnf(c_0_44, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_34, c_0_19])).
% 0.47/0.68  fof(c_0_45, plain, ![X8, X9]:(~r1_xboole_0(X8,X9)|r1_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.47/0.68  cnf(c_0_46, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_35, c_0_19])).
% 0.47/0.68  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_27]), c_0_38]), c_0_39])).
% 0.47/0.68  cnf(c_0_48, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_27]), c_0_37]), c_0_41])])).
% 0.47/0.68  fof(c_0_49, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)&~r1_xboole_0(k3_xboole_0(esk4_0,esk2_0),k3_xboole_0(esk4_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).
% 0.47/0.68  cnf(c_0_50, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X4,X3)))), inference(spm,[status(thm)],[c_0_43, c_0_36])).
% 0.47/0.68  cnf(c_0_51, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_44]), c_0_27])).
% 0.47/0.68  cnf(c_0_52, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.47/0.68  cnf(c_0_53, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_37]), c_0_48])).
% 0.47/0.68  cnf(c_0_54, negated_conjecture, (~r1_xboole_0(k3_xboole_0(esk4_0,esk2_0),k3_xboole_0(esk4_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.47/0.68  cnf(c_0_55, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X1,k4_xboole_0(X2,X4))|~r1_xboole_0(X4,X3)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.47/0.68  cnf(c_0_56, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.47/0.68  cnf(c_0_57, negated_conjecture, (~r1_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk2_0)),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_19]), c_0_19])).
% 0.47/0.68  cnf(c_0_58, plain, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(X2,k4_xboole_0(X2,X4)))|~r1_xboole_0(X3,X4)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.47/0.68  cnf(c_0_59, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.47/0.68  cnf(c_0_60, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])]), ['proof']).
% 0.47/0.68  # SZS output end CNFRefutation
% 0.47/0.68  # Proof object total steps             : 61
% 0.47/0.68  # Proof object clause steps            : 34
% 0.47/0.68  # Proof object formula steps           : 27
% 0.47/0.68  # Proof object conjectures             : 7
% 0.47/0.68  # Proof object clause conjectures      : 4
% 0.47/0.68  # Proof object formula conjectures     : 3
% 0.47/0.68  # Proof object initial clauses used    : 15
% 0.47/0.68  # Proof object initial formulas used   : 13
% 0.47/0.68  # Proof object generating inferences   : 10
% 0.47/0.68  # Proof object simplifying inferences  : 21
% 0.47/0.68  # Training examples: 0 positive, 0 negative
% 0.47/0.68  # Parsed axioms                        : 13
% 0.47/0.68  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.68  # Initial clauses                      : 18
% 0.47/0.68  # Removed in clause preprocessing      : 1
% 0.47/0.68  # Initial clauses in saturation        : 17
% 0.47/0.68  # Processed clauses                    : 5187
% 0.47/0.68  # ...of these trivial                  : 28
% 0.47/0.68  # ...subsumed                          : 4692
% 0.47/0.68  # ...remaining for further processing  : 467
% 0.47/0.68  # Other redundant clauses eliminated   : 0
% 0.47/0.68  # Clauses deleted for lack of memory   : 0
% 0.47/0.68  # Backward-subsumed                    : 23
% 0.47/0.68  # Backward-rewritten                   : 12
% 0.47/0.68  # Generated clauses                    : 39039
% 0.47/0.68  # ...of the previous two non-trivial   : 32145
% 0.47/0.68  # Contextual simplify-reflections      : 3
% 0.47/0.68  # Paramodulations                      : 39039
% 0.47/0.68  # Factorizations                       : 0
% 0.47/0.68  # Equation resolutions                 : 0
% 0.47/0.68  # Propositional unsat checks           : 0
% 0.47/0.68  #    Propositional check models        : 0
% 0.47/0.68  #    Propositional check unsatisfiable : 0
% 0.47/0.68  #    Propositional clauses             : 0
% 0.47/0.68  #    Propositional clauses after purity: 0
% 0.47/0.68  #    Propositional unsat core size     : 0
% 0.47/0.68  #    Propositional preprocessing time  : 0.000
% 0.47/0.68  #    Propositional encoding time       : 0.000
% 0.47/0.68  #    Propositional solver time         : 0.000
% 0.47/0.68  #    Success case prop preproc time    : 0.000
% 0.47/0.68  #    Success case prop encoding time   : 0.000
% 0.47/0.68  #    Success case prop solver time     : 0.000
% 0.47/0.68  # Current number of processed clauses  : 415
% 0.47/0.68  #    Positive orientable unit clauses  : 53
% 0.47/0.68  #    Positive unorientable unit clauses: 3
% 0.47/0.68  #    Negative unit clauses             : 58
% 0.47/0.68  #    Non-unit-clauses                  : 301
% 0.47/0.68  # Current number of unprocessed clauses: 26664
% 0.47/0.68  # ...number of literals in the above   : 66873
% 0.47/0.68  # Current number of archived formulas  : 0
% 0.47/0.68  # Current number of archived clauses   : 53
% 0.47/0.68  # Clause-clause subsumption calls (NU) : 17974
% 0.47/0.68  # Rec. Clause-clause subsumption calls : 16808
% 0.47/0.68  # Non-unit clause-clause subsumptions  : 2458
% 0.47/0.68  # Unit Clause-clause subsumption calls : 907
% 0.47/0.68  # Rewrite failures with RHS unbound    : 0
% 0.47/0.68  # BW rewrite match attempts            : 355
% 0.47/0.68  # BW rewrite match successes           : 28
% 0.47/0.68  # Condensation attempts                : 0
% 0.47/0.68  # Condensation successes               : 0
% 0.47/0.68  # Termbank termtop insertions          : 406616
% 0.47/0.68  
% 0.47/0.68  # -------------------------------------------------
% 0.47/0.68  # User time                : 0.317 s
% 0.47/0.68  # System time              : 0.022 s
% 0.47/0.68  # Total time               : 0.339 s
% 0.47/0.68  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
