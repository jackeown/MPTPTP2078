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
% DateTime   : Thu Dec  3 10:33:42 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 753 expanded)
%              Number of clauses        :   38 ( 330 expanded)
%              Number of leaves         :   15 ( 210 expanded)
%              Depth                    :   12
%              Number of atoms          :   95 ( 809 expanded)
%              Number of equality atoms :   54 ( 729 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t78_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t81_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
     => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(t80_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t83_xboole_1,conjecture,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(c_0_15,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_16,plain,(
    ! [X26,X27] : k4_xboole_0(X26,k4_xboole_0(X26,X27)) = k3_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_17,plain,(
    ! [X19,X20] : k4_xboole_0(k2_xboole_0(X19,X20),X20) = k4_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_18,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_19,plain,(
    ! [X13,X14] : k3_xboole_0(X13,k2_xboole_0(X13,X14)) = X13 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_20,plain,(
    ! [X17,X18] : k2_xboole_0(X17,k4_xboole_0(X18,X17)) = k2_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X28,X29,X30] : k3_xboole_0(X28,k4_xboole_0(X29,X30)) = k4_xboole_0(k3_xboole_0(X28,X29),X30) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_28,plain,(
    ! [X34,X35,X36] :
      ( ~ r1_xboole_0(X34,X35)
      | k3_xboole_0(X34,k2_xboole_0(X35,X36)) = k3_xboole_0(X34,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).

fof(c_0_29,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k3_xboole_0(X24,X25)) = k4_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_22])).

cnf(c_0_31,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_25,c_0_22])).

cnf(c_0_33,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_26])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_22]),c_0_22])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3))) = k4_xboole_0(X1,k4_xboole_0(X1,X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_22]),c_0_22])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_22])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_33,c_0_37])).

fof(c_0_42,plain,(
    ! [X44,X45,X46] :
      ( ~ r1_xboole_0(X44,k4_xboole_0(X45,X46))
      | r1_xboole_0(X45,k4_xboole_0(X44,X46)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X4))))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X4))))))
    | ~ r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_38]),c_0_38]),c_0_38])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_30])).

cnf(c_0_45,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X2 ),
    inference(spm,[status(thm)],[c_0_41,c_0_24])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X2,k4_xboole_0(X1,X3))
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_47,plain,(
    ! [X41,X42,X43] :
      ( ~ r1_xboole_0(X41,X42)
      | r1_xboole_0(X41,k4_xboole_0(X42,X43)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_xboole_1])])).

fof(c_0_48,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k2_xboole_0(X11,X12) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_49,plain,(
    ! [X15,X16] : r1_tarski(k4_xboole_0(X15,X16),X15) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_37]),c_0_37]),c_0_23]),c_0_45]),c_0_23]),c_0_45]),c_0_23]),c_0_45]),c_0_37])).

cnf(c_0_51,plain,
    ( r1_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X2))
    | ~ r1_xboole_0(X3,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_23])).

cnf(c_0_52,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_26]),c_0_31])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_56,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_xboole_0(X1,X2)
      <=> k4_xboole_0(X1,X2) = X1 ) ),
    inference(assume_negation,[status(cth)],[t83_xboole_1])).

cnf(c_0_57,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_24]),c_0_26]),c_0_52])).

cnf(c_0_58,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_53,c_0_30])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_24])).

fof(c_0_60,negated_conjecture,
    ( ( ~ r1_xboole_0(esk1_0,esk2_0)
      | k4_xboole_0(esk1_0,esk2_0) != esk1_0 )
    & ( r1_xboole_0(esk1_0,esk2_0)
      | k4_xboole_0(esk1_0,esk2_0) = esk1_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_56])])])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_24]),c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk2_0)
    | k4_xboole_0(esk1_0,esk2_0) = esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_63,plain,(
    ! [X37,X38] : r1_xboole_0(k4_xboole_0(X37,X38),X38) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0)
    | k4_xboole_0(esk1_0,esk2_0) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65])])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_65]),c_0_67]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:32:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.47  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.20/0.47  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.47  #
% 0.20/0.47  # Preprocessing time       : 0.027 s
% 0.20/0.47  # Presaturation interreduction done
% 0.20/0.47  
% 0.20/0.47  # Proof found!
% 0.20/0.47  # SZS status Theorem
% 0.20/0.47  # SZS output start CNFRefutation
% 0.20/0.47  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.47  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.47  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.20/0.47  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.47  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.20/0.47  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.20/0.47  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.20/0.47  fof(t78_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 0.20/0.47  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.20/0.47  fof(t81_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 0.20/0.47  fof(t80_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_xboole_1)).
% 0.20/0.47  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.47  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.47  fof(t83_xboole_1, conjecture, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.47  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.20/0.47  fof(c_0_15, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.47  fof(c_0_16, plain, ![X26, X27]:k4_xboole_0(X26,k4_xboole_0(X26,X27))=k3_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.47  fof(c_0_17, plain, ![X19, X20]:k4_xboole_0(k2_xboole_0(X19,X20),X20)=k4_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.20/0.47  fof(c_0_18, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.47  fof(c_0_19, plain, ![X13, X14]:k3_xboole_0(X13,k2_xboole_0(X13,X14))=X13, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.20/0.47  fof(c_0_20, plain, ![X17, X18]:k2_xboole_0(X17,k4_xboole_0(X18,X17))=k2_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.20/0.47  cnf(c_0_21, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.47  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.47  cnf(c_0_23, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.47  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.47  cnf(c_0_25, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.47  cnf(c_0_26, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.47  fof(c_0_27, plain, ![X28, X29, X30]:k3_xboole_0(X28,k4_xboole_0(X29,X30))=k4_xboole_0(k3_xboole_0(X28,X29),X30), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.20/0.47  fof(c_0_28, plain, ![X34, X35, X36]:(~r1_xboole_0(X34,X35)|k3_xboole_0(X34,k2_xboole_0(X35,X36))=k3_xboole_0(X34,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).
% 0.20/0.47  fof(c_0_29, plain, ![X24, X25]:k4_xboole_0(X24,k3_xboole_0(X24,X25))=k4_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.20/0.47  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_22])).
% 0.20/0.47  cnf(c_0_31, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.47  cnf(c_0_32, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_25, c_0_22])).
% 0.20/0.47  cnf(c_0_33, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_23, c_0_26])).
% 0.20/0.47  cnf(c_0_34, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.47  cnf(c_0_35, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.47  cnf(c_0_36, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.47  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])).
% 0.20/0.47  cnf(c_0_38, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_22]), c_0_22])).
% 0.20/0.47  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3)))=k4_xboole_0(X1,k4_xboole_0(X1,X3))|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_22]), c_0_22])).
% 0.20/0.47  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_36, c_0_22])).
% 0.20/0.47  cnf(c_0_41, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[c_0_33, c_0_37])).
% 0.20/0.47  fof(c_0_42, plain, ![X44, X45, X46]:(~r1_xboole_0(X44,k4_xboole_0(X45,X46))|r1_xboole_0(X45,k4_xboole_0(X44,X46))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).
% 0.20/0.47  cnf(c_0_43, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X4)))))))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X4))))))|~r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_38]), c_0_38]), c_0_38])).
% 0.20/0.47  cnf(c_0_44, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_30])).
% 0.20/0.47  cnf(c_0_45, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X2), inference(spm,[status(thm)],[c_0_41, c_0_24])).
% 0.20/0.47  cnf(c_0_46, plain, (r1_xboole_0(X2,k4_xboole_0(X1,X3))|~r1_xboole_0(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.47  fof(c_0_47, plain, ![X41, X42, X43]:(~r1_xboole_0(X41,X42)|r1_xboole_0(X41,k4_xboole_0(X42,X43))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_xboole_1])])).
% 0.20/0.47  fof(c_0_48, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k2_xboole_0(X11,X12)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.47  fof(c_0_49, plain, ![X15, X16]:r1_tarski(k4_xboole_0(X15,X16),X15), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.47  cnf(c_0_50, plain, (k2_xboole_0(X1,X2)=X2|~r1_xboole_0(k2_xboole_0(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_37]), c_0_37]), c_0_23]), c_0_45]), c_0_23]), c_0_45]), c_0_23]), c_0_45]), c_0_37])).
% 0.20/0.47  cnf(c_0_51, plain, (r1_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X2))|~r1_xboole_0(X3,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_46, c_0_23])).
% 0.20/0.47  cnf(c_0_52, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_26]), c_0_31])).
% 0.20/0.47  cnf(c_0_53, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.47  cnf(c_0_54, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.47  cnf(c_0_55, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.47  fof(c_0_56, negated_conjecture, ~(![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1)), inference(assume_negation,[status(cth)],[t83_xboole_1])).
% 0.20/0.47  cnf(c_0_57, plain, (k2_xboole_0(X1,X2)=X1|~r1_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_24]), c_0_26]), c_0_52])).
% 0.20/0.47  cnf(c_0_58, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_53, c_0_30])).
% 0.20/0.47  cnf(c_0_59, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_24])).
% 0.20/0.47  fof(c_0_60, negated_conjecture, ((~r1_xboole_0(esk1_0,esk2_0)|k4_xboole_0(esk1_0,esk2_0)!=esk1_0)&(r1_xboole_0(esk1_0,esk2_0)|k4_xboole_0(esk1_0,esk2_0)=esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_56])])])).
% 0.20/0.47  cnf(c_0_61, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_24]), c_0_59])).
% 0.20/0.47  cnf(c_0_62, negated_conjecture, (r1_xboole_0(esk1_0,esk2_0)|k4_xboole_0(esk1_0,esk2_0)=esk1_0), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.47  fof(c_0_63, plain, ![X37, X38]:r1_xboole_0(k4_xboole_0(X37,X38),X38), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.20/0.47  cnf(c_0_64, negated_conjecture, (~r1_xboole_0(esk1_0,esk2_0)|k4_xboole_0(esk1_0,esk2_0)!=esk1_0), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.47  cnf(c_0_65, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)=esk1_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.47  cnf(c_0_66, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.47  cnf(c_0_67, negated_conjecture, (~r1_xboole_0(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65])])).
% 0.20/0.47  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_65]), c_0_67]), ['proof']).
% 0.20/0.47  # SZS output end CNFRefutation
% 0.20/0.47  # Proof object total steps             : 69
% 0.20/0.47  # Proof object clause steps            : 38
% 0.20/0.47  # Proof object formula steps           : 31
% 0.20/0.47  # Proof object conjectures             : 8
% 0.20/0.47  # Proof object clause conjectures      : 5
% 0.20/0.47  # Proof object formula conjectures     : 3
% 0.20/0.47  # Proof object initial clauses used    : 16
% 0.20/0.47  # Proof object initial formulas used   : 15
% 0.20/0.47  # Proof object generating inferences   : 15
% 0.20/0.47  # Proof object simplifying inferences  : 33
% 0.20/0.47  # Training examples: 0 positive, 0 negative
% 0.20/0.47  # Parsed axioms                        : 20
% 0.20/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.47  # Initial clauses                      : 21
% 0.20/0.47  # Removed in clause preprocessing      : 1
% 0.20/0.47  # Initial clauses in saturation        : 20
% 0.20/0.47  # Processed clauses                    : 949
% 0.20/0.47  # ...of these trivial                  : 52
% 0.20/0.47  # ...subsumed                          : 668
% 0.20/0.47  # ...remaining for further processing  : 228
% 0.20/0.47  # Other redundant clauses eliminated   : 0
% 0.20/0.47  # Clauses deleted for lack of memory   : 0
% 0.20/0.47  # Backward-subsumed                    : 13
% 0.20/0.47  # Backward-rewritten                   : 20
% 0.20/0.47  # Generated clauses                    : 8629
% 0.20/0.47  # ...of the previous two non-trivial   : 6019
% 0.20/0.47  # Contextual simplify-reflections      : 0
% 0.20/0.47  # Paramodulations                      : 8629
% 0.20/0.47  # Factorizations                       : 0
% 0.20/0.47  # Equation resolutions                 : 0
% 0.20/0.47  # Propositional unsat checks           : 0
% 0.20/0.47  #    Propositional check models        : 0
% 0.20/0.47  #    Propositional check unsatisfiable : 0
% 0.20/0.47  #    Propositional clauses             : 0
% 0.20/0.47  #    Propositional clauses after purity: 0
% 0.20/0.47  #    Propositional unsat core size     : 0
% 0.20/0.47  #    Propositional preprocessing time  : 0.000
% 0.20/0.47  #    Propositional encoding time       : 0.000
% 0.20/0.47  #    Propositional solver time         : 0.000
% 0.20/0.47  #    Success case prop preproc time    : 0.000
% 0.20/0.47  #    Success case prop encoding time   : 0.000
% 0.20/0.47  #    Success case prop solver time     : 0.000
% 0.20/0.47  # Current number of processed clauses  : 175
% 0.20/0.47  #    Positive orientable unit clauses  : 59
% 0.20/0.47  #    Positive unorientable unit clauses: 5
% 0.20/0.47  #    Negative unit clauses             : 1
% 0.20/0.47  #    Non-unit-clauses                  : 110
% 0.20/0.47  # Current number of unprocessed clauses: 5032
% 0.20/0.47  # ...number of literals in the above   : 8879
% 0.20/0.47  # Current number of archived formulas  : 0
% 0.20/0.47  # Current number of archived clauses   : 54
% 0.20/0.47  # Clause-clause subsumption calls (NU) : 3982
% 0.20/0.47  # Rec. Clause-clause subsumption calls : 3982
% 0.20/0.47  # Non-unit clause-clause subsumptions  : 586
% 0.20/0.47  # Unit Clause-clause subsumption calls : 84
% 0.20/0.47  # Rewrite failures with RHS unbound    : 20
% 0.20/0.47  # BW rewrite match attempts            : 500
% 0.20/0.47  # BW rewrite match successes           : 77
% 0.20/0.47  # Condensation attempts                : 0
% 0.20/0.47  # Condensation successes               : 0
% 0.20/0.47  # Termbank termtop insertions          : 90279
% 0.20/0.47  
% 0.20/0.47  # -------------------------------------------------
% 0.20/0.47  # User time                : 0.123 s
% 0.20/0.47  # System time              : 0.010 s
% 0.20/0.47  # Total time               : 0.133 s
% 0.20/0.47  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
