%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:54 EST 2020

% Result     : Theorem 12.71s
% Output     : CNFRefutation 12.71s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 395 expanded)
%              Number of clauses        :   38 ( 178 expanded)
%              Number of leaves         :   13 ( 106 expanded)
%              Depth                    :   12
%              Number of atoms          :  104 ( 501 expanded)
%              Number of equality atoms :   35 ( 312 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t18_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k3_xboole_0(X2,X3))
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t110_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k5_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

fof(t97_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(k4_xboole_0(X1,X2),X3)
        & r1_tarski(k4_xboole_0(X2,X1),X3) )
     => r1_tarski(k5_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_xboole_1)).

fof(c_0_13,plain,(
    ! [X4,X5] : k5_xboole_0(X4,X5) = k5_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_14,plain,(
    ! [X31,X32,X33] : k5_xboole_0(k5_xboole_0(X31,X32),X33) = k5_xboole_0(X31,k5_xboole_0(X32,X33)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_15,plain,(
    ! [X40,X41] : k2_xboole_0(X40,X41) = k5_xboole_0(X40,k4_xboole_0(X41,X40)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_16,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_17,plain,(
    ! [X28,X29] : r1_tarski(k4_xboole_0(X28,X29),X28) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_18,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X34] : k5_xboole_0(X34,X34) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_21,plain,(
    ! [X30] : k5_xboole_0(X30,k1_xboole_0) = X30 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_22,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k2_xboole_0(X18,X19) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_25,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,k3_xboole_0(X24,X25))
      | r1_tarski(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).

cnf(c_0_26,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_27,plain,(
    ! [X20,X21,X22] : k3_xboole_0(k3_xboole_0(X20,X21),X22) = k3_xboole_0(X20,k3_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_35,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_36,plain,(
    ! [X26,X27] :
      ( ~ r1_tarski(X26,X27)
      | k3_xboole_0(X26,X27) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_37,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X2) )
       => r1_tarski(k5_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t110_xboole_1])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( r1_tarski(k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_42,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    & r1_tarski(esk5_0,esk4_0)
    & ~ r1_tarski(k5_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_19]),c_0_38])).

cnf(c_0_44,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_29])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,X3)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_43])).

fof(c_0_49,plain,(
    ! [X37,X38,X39] :
      ( ~ r1_tarski(k4_xboole_0(X37,X38),X39)
      | ~ r1_tarski(k4_xboole_0(X38,X37),X39)
      | r1_tarski(k5_xboole_0(X37,X38),X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_xboole_1])])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_30]),c_0_47])])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X3,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X3)
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(k4_xboole_0(X2,X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_43])).

cnf(c_0_55,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( k3_xboole_0(esk4_0,X1) = X1
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X3)
    | ~ r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X3)
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_24]),c_0_24])).

cnf(c_0_58,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_54,c_0_34])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X3)
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,X1),esk4_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_46])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,X1),esk4_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_55])])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:51:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 12.71/12.97  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 12.71/12.97  # and selection function SelectMaxLComplexAvoidPosPred.
% 12.71/12.97  #
% 12.71/12.97  # Preprocessing time       : 0.027 s
% 12.71/12.97  
% 12.71/12.97  # Proof found!
% 12.71/12.97  # SZS status Theorem
% 12.71/12.97  # SZS output start CNFRefutation
% 12.71/12.97  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 12.71/12.97  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 12.71/12.97  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 12.71/12.97  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.71/12.97  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 12.71/12.97  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 12.71/12.97  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 12.71/12.97  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 12.71/12.97  fof(t18_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k3_xboole_0(X2,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 12.71/12.97  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 12.71/12.97  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 12.71/12.97  fof(t110_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k5_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 12.71/12.97  fof(t97_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(k4_xboole_0(X1,X2),X3)&r1_tarski(k4_xboole_0(X2,X1),X3))=>r1_tarski(k5_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_xboole_1)).
% 12.71/12.97  fof(c_0_13, plain, ![X4, X5]:k5_xboole_0(X4,X5)=k5_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 12.71/12.97  fof(c_0_14, plain, ![X31, X32, X33]:k5_xboole_0(k5_xboole_0(X31,X32),X33)=k5_xboole_0(X31,k5_xboole_0(X32,X33)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 12.71/12.97  fof(c_0_15, plain, ![X40, X41]:k2_xboole_0(X40,X41)=k5_xboole_0(X40,k4_xboole_0(X41,X40)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 12.71/12.97  fof(c_0_16, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 12.71/12.97  fof(c_0_17, plain, ![X28, X29]:r1_tarski(k4_xboole_0(X28,X29),X28), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 12.71/12.97  cnf(c_0_18, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 12.71/12.97  cnf(c_0_19, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 12.71/12.97  fof(c_0_20, plain, ![X34]:k5_xboole_0(X34,X34)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 12.71/12.97  fof(c_0_21, plain, ![X30]:k5_xboole_0(X30,k1_xboole_0)=X30, inference(variable_rename,[status(thm)],[t5_boole])).
% 12.71/12.97  fof(c_0_22, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k2_xboole_0(X18,X19)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 12.71/12.97  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 12.71/12.97  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 12.71/12.97  fof(c_0_25, plain, ![X23, X24, X25]:(~r1_tarski(X23,k3_xboole_0(X24,X25))|r1_tarski(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_xboole_1])])).
% 12.71/12.97  cnf(c_0_26, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 12.71/12.97  fof(c_0_27, plain, ![X20, X21, X22]:k3_xboole_0(k3_xboole_0(X20,X21),X22)=k3_xboole_0(X20,k3_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 12.71/12.97  cnf(c_0_28, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X3,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 12.71/12.97  cnf(c_0_29, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 12.71/12.97  cnf(c_0_30, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 12.71/12.97  cnf(c_0_31, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 12.71/12.97  cnf(c_0_32, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 12.71/12.97  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 12.71/12.97  cnf(c_0_34, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_26, c_0_24])).
% 12.71/12.97  cnf(c_0_35, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 12.71/12.97  fof(c_0_36, plain, ![X26, X27]:(~r1_tarski(X26,X27)|k3_xboole_0(X26,X27)=X26), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 12.71/12.97  fof(c_0_37, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k5_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t110_xboole_1])).
% 12.71/12.97  cnf(c_0_38, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 12.71/12.97  cnf(c_0_39, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 12.71/12.97  cnf(c_0_40, plain, (r1_tarski(k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 12.71/12.97  cnf(c_0_41, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 12.71/12.97  fof(c_0_42, negated_conjecture, ((r1_tarski(esk3_0,esk4_0)&r1_tarski(esk5_0,esk4_0))&~r1_tarski(k5_xboole_0(esk3_0,esk5_0),esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).
% 12.71/12.97  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_19]), c_0_38])).
% 12.71/12.97  cnf(c_0_44, plain, (r1_tarski(k1_xboole_0,X1)|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_29])).
% 12.71/12.97  cnf(c_0_45, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 12.71/12.97  cnf(c_0_46, plain, (r1_tarski(k5_xboole_0(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_43])).
% 12.71/12.97  cnf(c_0_47, negated_conjecture, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 12.71/12.97  cnf(c_0_48, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,X3)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_35, c_0_43])).
% 12.71/12.97  fof(c_0_49, plain, ![X37, X38, X39]:(~r1_tarski(k4_xboole_0(X37,X38),X39)|~r1_tarski(k4_xboole_0(X38,X37),X39)|r1_tarski(k5_xboole_0(X37,X38),X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_xboole_1])])).
% 12.71/12.97  cnf(c_0_50, plain, (r1_tarski(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_30]), c_0_47])])).
% 12.71/12.97  cnf(c_0_51, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X3,X1)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_48, c_0_43])).
% 12.71/12.97  cnf(c_0_52, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 12.71/12.97  cnf(c_0_53, plain, (r1_tarski(k5_xboole_0(X1,X2),X3)|~r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(k4_xboole_0(X2,X1),X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 12.71/12.97  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_33, c_0_43])).
% 12.71/12.97  cnf(c_0_55, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_33, c_0_50])).
% 12.71/12.97  cnf(c_0_56, negated_conjecture, (k3_xboole_0(esk4_0,X1)=X1|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 12.71/12.97  cnf(c_0_57, plain, (r1_tarski(k5_xboole_0(X1,X2),X3)|~r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X3)|~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_24]), c_0_24])).
% 12.71/12.97  cnf(c_0_58, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_54, c_0_34])).
% 12.71/12.97  cnf(c_0_59, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 12.71/12.97  cnf(c_0_60, plain, (r1_tarski(k5_xboole_0(X1,X2),X3)|~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 12.71/12.97  cnf(c_0_61, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,X1),esk4_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_59, c_0_46])).
% 12.71/12.97  cnf(c_0_62, negated_conjecture, (~r1_tarski(k5_xboole_0(esk3_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 12.71/12.97  cnf(c_0_63, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,X1),esk4_0)|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_55])])).
% 12.71/12.97  cnf(c_0_64, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_45])]), ['proof']).
% 12.71/12.97  # SZS output end CNFRefutation
% 12.71/12.97  # Proof object total steps             : 65
% 12.71/12.97  # Proof object clause steps            : 38
% 12.71/12.97  # Proof object formula steps           : 27
% 12.71/12.97  # Proof object conjectures             : 12
% 12.71/12.97  # Proof object clause conjectures      : 9
% 12.71/12.97  # Proof object formula conjectures     : 3
% 12.71/12.97  # Proof object initial clauses used    : 15
% 12.71/12.97  # Proof object initial formulas used   : 13
% 12.71/12.97  # Proof object generating inferences   : 19
% 12.71/12.97  # Proof object simplifying inferences  : 16
% 12.71/12.97  # Training examples: 0 positive, 0 negative
% 12.71/12.97  # Parsed axioms                        : 17
% 12.71/12.97  # Removed by relevancy pruning/SinE    : 0
% 12.71/12.97  # Initial clauses                      : 20
% 12.71/12.97  # Removed in clause preprocessing      : 2
% 12.71/12.97  # Initial clauses in saturation        : 18
% 12.71/12.97  # Processed clauses                    : 23200
% 12.71/12.97  # ...of these trivial                  : 911
% 12.71/12.97  # ...subsumed                          : 19440
% 12.71/12.97  # ...remaining for further processing  : 2849
% 12.71/12.97  # Other redundant clauses eliminated   : 0
% 12.71/12.97  # Clauses deleted for lack of memory   : 0
% 12.71/12.97  # Backward-subsumed                    : 130
% 12.71/12.97  # Backward-rewritten                   : 70
% 12.71/12.97  # Generated clauses                    : 1379767
% 12.71/12.97  # ...of the previous two non-trivial   : 1327558
% 12.71/12.97  # Contextual simplify-reflections      : 43
% 12.71/12.97  # Paramodulations                      : 1379761
% 12.71/12.97  # Factorizations                       : 0
% 12.71/12.97  # Equation resolutions                 : 0
% 12.71/12.97  # Propositional unsat checks           : 0
% 12.71/12.97  #    Propositional check models        : 0
% 12.71/12.97  #    Propositional check unsatisfiable : 0
% 12.71/12.97  #    Propositional clauses             : 0
% 12.71/12.97  #    Propositional clauses after purity: 0
% 12.71/12.97  #    Propositional unsat core size     : 0
% 12.71/12.97  #    Propositional preprocessing time  : 0.000
% 12.71/12.97  #    Propositional encoding time       : 0.000
% 12.71/12.97  #    Propositional solver time         : 0.000
% 12.71/12.97  #    Success case prop preproc time    : 0.000
% 12.71/12.97  #    Success case prop encoding time   : 0.000
% 12.71/12.97  #    Success case prop solver time     : 0.000
% 12.71/12.97  # Current number of processed clauses  : 2647
% 12.71/12.97  #    Positive orientable unit clauses  : 175
% 12.71/12.97  #    Positive unorientable unit clauses: 10
% 12.71/12.97  #    Negative unit clauses             : 14
% 12.71/12.97  #    Non-unit-clauses                  : 2448
% 12.71/12.97  # Current number of unprocessed clauses: 1298993
% 12.71/12.97  # ...number of literals in the above   : 4552907
% 12.71/12.97  # Current number of archived formulas  : 0
% 12.71/12.97  # Current number of archived clauses   : 202
% 12.71/12.97  # Clause-clause subsumption calls (NU) : 799561
% 12.71/12.97  # Rec. Clause-clause subsumption calls : 713121
% 12.71/12.97  # Non-unit clause-clause subsumptions  : 15361
% 12.71/12.97  # Unit Clause-clause subsumption calls : 14290
% 12.71/12.97  # Rewrite failures with RHS unbound    : 0
% 12.71/12.97  # BW rewrite match attempts            : 5351
% 12.71/12.97  # BW rewrite match successes           : 238
% 12.71/12.97  # Condensation attempts                : 0
% 12.71/12.97  # Condensation successes               : 0
% 12.71/12.97  # Termbank termtop insertions          : 29101368
% 12.86/13.03  
% 12.86/13.03  # -------------------------------------------------
% 12.86/13.03  # User time                : 12.065 s
% 12.86/13.03  # System time              : 0.615 s
% 12.86/13.03  # Total time               : 12.679 s
% 12.86/13.03  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
