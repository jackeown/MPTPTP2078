%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:47 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 237 expanded)
%              Number of clauses        :   34 ( 103 expanded)
%              Number of leaves         :   10 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :  112 ( 603 expanded)
%              Number of equality atoms :   39 ( 157 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t67_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X2,X3) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t15_xboole_1,axiom,(
    ! [X1,X2] :
      ( k2_xboole_0(X1,X2) = k1_xboole_0
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t20_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & ! [X4] :
            ( ( r1_tarski(X4,X2)
              & r1_tarski(X4,X3) )
           => r1_tarski(X4,X1) ) )
     => X1 = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_xboole_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X1,X3)
          & r1_xboole_0(X2,X3) )
       => X1 = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t67_xboole_1])).

fof(c_0_11,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r1_xboole_0(X7,X8)
        | r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)) )
      & ( ~ r2_hidden(X12,k3_xboole_0(X10,X11))
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_12,plain,(
    ! [X13] :
      ( X13 = k1_xboole_0
      | r2_hidden(esk2_1(X13),X13) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_13,plain,(
    ! [X5,X6] :
      ( ~ r1_xboole_0(X5,X6)
      | r1_xboole_0(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_14,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0)
    & r1_tarski(esk4_0,esk6_0)
    & r1_xboole_0(esk5_0,esk6_0)
    & esk4_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X15,X16] :
      ( k2_xboole_0(X15,X16) != k1_xboole_0
      | X15 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_xboole_1])])).

fof(c_0_18,plain,(
    ! [X27,X28] : k2_xboole_0(k3_xboole_0(X27,X28),k4_xboole_0(X27,X28)) = X27 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X24,X25] : r1_tarski(k4_xboole_0(X24,X25),X24) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_22,plain,(
    ! [X26] : k4_xboole_0(X26,k1_xboole_0) = X26 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_23,plain,(
    ! [X17,X18,X19] : k3_xboole_0(k3_xboole_0(X17,X18),X19) = k3_xboole_0(X17,k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | k2_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_28,plain,(
    ! [X20,X21,X22] :
      ( ( r1_tarski(esk3_3(X20,X21,X22),X21)
        | ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X20,X22)
        | X20 = k3_xboole_0(X21,X22) )
      & ( r1_tarski(esk3_3(X20,X21,X22),X22)
        | ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X20,X22)
        | X20 = k3_xboole_0(X21,X22) )
      & ( ~ r1_tarski(esk3_3(X20,X21,X22),X20)
        | ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X20,X22)
        | X20 = k3_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_xboole_1])])])])).

cnf(c_0_29,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk6_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_20])).

cnf(c_0_33,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_34,negated_conjecture,
    ( k3_xboole_0(esk6_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_27])).

cnf(c_0_35,plain,
    ( r1_tarski(esk3_3(X1,X2,X3),X3)
    | X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,negated_conjecture,
    ( k3_xboole_0(esk5_0,k3_xboole_0(esk6_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_34]),c_0_27])])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r1_tarski(esk3_3(X2,X1,X2),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(esk5_0,k3_xboole_0(esk6_0,X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_43,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(esk3_3(X1,X2,X3),X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_44,negated_conjecture,
    ( k3_xboole_0(esk6_0,esk4_0) = esk4_0
    | r1_tarski(esk3_3(esk4_0,esk6_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk6_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( k3_xboole_0(esk6_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_36]),c_0_41])])).

cnf(c_0_47,plain,
    ( r1_tarski(esk3_3(X1,X2,X3),X2)
    | X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( k3_xboole_0(X1,esk5_0) = esk4_0
    | r1_tarski(esk3_3(esk4_0,X1,esk5_0),X1)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk3_3(esk4_0,esk4_0,esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_36]),c_0_51]),c_0_52])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_53]),c_0_51]),c_0_48]),c_0_36])]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n024.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 15:08:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EI
% 0.19/0.37  # and selection function SelectLComplex.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t67_xboole_1, conjecture, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&r1_xboole_0(X2,X3))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 0.19/0.37  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.37  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.37  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.37  fof(t15_xboole_1, axiom, ![X1, X2]:(k2_xboole_0(X1,X2)=k1_xboole_0=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 0.19/0.37  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.19/0.37  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.37  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.37  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.19/0.37  fof(t20_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&![X4]:((r1_tarski(X4,X2)&r1_tarski(X4,X3))=>r1_tarski(X4,X1)))=>X1=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_xboole_1)).
% 0.19/0.37  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&r1_xboole_0(X2,X3))=>X1=k1_xboole_0)), inference(assume_negation,[status(cth)],[t67_xboole_1])).
% 0.19/0.37  fof(c_0_11, plain, ![X7, X8, X10, X11, X12]:((r1_xboole_0(X7,X8)|r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)))&(~r2_hidden(X12,k3_xboole_0(X10,X11))|~r1_xboole_0(X10,X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.37  fof(c_0_12, plain, ![X13]:(X13=k1_xboole_0|r2_hidden(esk2_1(X13),X13)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.37  fof(c_0_13, plain, ![X5, X6]:(~r1_xboole_0(X5,X6)|r1_xboole_0(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.37  fof(c_0_14, negated_conjecture, (((r1_tarski(esk4_0,esk5_0)&r1_tarski(esk4_0,esk6_0))&r1_xboole_0(esk5_0,esk6_0))&esk4_0!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.19/0.37  cnf(c_0_15, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_16, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  fof(c_0_17, plain, ![X15, X16]:(k2_xboole_0(X15,X16)!=k1_xboole_0|X15=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_xboole_1])])).
% 0.19/0.37  fof(c_0_18, plain, ![X27, X28]:k2_xboole_0(k3_xboole_0(X27,X28),k4_xboole_0(X27,X28))=X27, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.19/0.37  cnf(c_0_19, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (r1_xboole_0(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  fof(c_0_21, plain, ![X24, X25]:r1_tarski(k4_xboole_0(X24,X25),X24), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.37  fof(c_0_22, plain, ![X26]:k4_xboole_0(X26,k1_xboole_0)=X26, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.37  fof(c_0_23, plain, ![X17, X18, X19]:k3_xboole_0(k3_xboole_0(X17,X18),X19)=k3_xboole_0(X17,k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.19/0.37  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.37  cnf(c_0_25, plain, (X1=k1_xboole_0|k2_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.37  cnf(c_0_26, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (r1_xboole_0(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.37  fof(c_0_28, plain, ![X20, X21, X22]:(((r1_tarski(esk3_3(X20,X21,X22),X21)|(~r1_tarski(X20,X21)|~r1_tarski(X20,X22))|X20=k3_xboole_0(X21,X22))&(r1_tarski(esk3_3(X20,X21,X22),X22)|(~r1_tarski(X20,X21)|~r1_tarski(X20,X22))|X20=k3_xboole_0(X21,X22)))&(~r1_tarski(esk3_3(X20,X21,X22),X20)|(~r1_tarski(X20,X21)|~r1_tarski(X20,X22))|X20=k3_xboole_0(X21,X22))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_xboole_1])])])])).
% 0.19/0.37  cnf(c_0_29, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_30, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_31, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, (k3_xboole_0(esk5_0,esk6_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_20])).
% 0.19/0.37  cnf(c_0_33, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26])])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (k3_xboole_0(esk6_0,esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_27])).
% 0.19/0.37  cnf(c_0_35, plain, (r1_tarski(esk3_3(X1,X2,X3),X3)|X1=k3_xboole_0(X2,X3)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.37  cnf(c_0_36, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.37  cnf(c_0_37, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (k3_xboole_0(esk5_0,k3_xboole_0(esk6_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.19/0.37  cnf(c_0_39, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_34]), c_0_27])])).
% 0.19/0.37  cnf(c_0_40, plain, (k3_xboole_0(X1,X2)=X2|r1_tarski(esk3_3(X2,X1,X2),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, (r1_tarski(esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_42, negated_conjecture, (r1_xboole_0(esk5_0,k3_xboole_0(esk6_0,X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.19/0.37  cnf(c_0_43, plain, (X1=k3_xboole_0(X2,X3)|~r1_tarski(esk3_3(X1,X2,X3),X1)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.37  cnf(c_0_44, negated_conjecture, (k3_xboole_0(esk6_0,esk4_0)=esk4_0|r1_tarski(esk3_3(esk4_0,esk6_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.37  cnf(c_0_45, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk6_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_19, c_0_42])).
% 0.19/0.37  cnf(c_0_46, negated_conjecture, (k3_xboole_0(esk6_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_36]), c_0_41])])).
% 0.19/0.37  cnf(c_0_47, plain, (r1_tarski(esk3_3(X1,X2,X3),X2)|X1=k3_xboole_0(X2,X3)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.37  cnf(c_0_48, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_49, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.37  cnf(c_0_50, negated_conjecture, (k3_xboole_0(X1,esk5_0)=esk4_0|r1_tarski(esk3_3(esk4_0,X1,esk5_0),X1)|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.37  cnf(c_0_51, negated_conjecture, (k3_xboole_0(esk4_0,esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_49])).
% 0.19/0.37  cnf(c_0_52, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_53, negated_conjecture, (r1_tarski(esk3_3(esk4_0,esk4_0,esk5_0),esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_36]), c_0_51]), c_0_52])).
% 0.19/0.37  cnf(c_0_54, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_53]), c_0_51]), c_0_48]), c_0_36])]), c_0_52]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 55
% 0.19/0.37  # Proof object clause steps            : 34
% 0.19/0.37  # Proof object formula steps           : 21
% 0.19/0.37  # Proof object conjectures             : 21
% 0.19/0.37  # Proof object clause conjectures      : 18
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 16
% 0.19/0.37  # Proof object initial formulas used   : 10
% 0.19/0.37  # Proof object generating inferences   : 18
% 0.19/0.37  # Proof object simplifying inferences  : 15
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 10
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 16
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 16
% 0.19/0.37  # Processed clauses                    : 222
% 0.19/0.37  # ...of these trivial                  : 18
% 0.19/0.37  # ...subsumed                          : 63
% 0.19/0.37  # ...remaining for further processing  : 141
% 0.19/0.37  # Other redundant clauses eliminated   : 1
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 1
% 0.19/0.37  # Backward-rewritten                   : 15
% 0.19/0.37  # Generated clauses                    : 757
% 0.19/0.37  # ...of the previous two non-trivial   : 366
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 756
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 1
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 109
% 0.19/0.37  #    Positive orientable unit clauses  : 73
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 3
% 0.19/0.37  #    Non-unit-clauses                  : 33
% 0.19/0.37  # Current number of unprocessed clauses: 167
% 0.19/0.37  # ...number of literals in the above   : 302
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 32
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 85
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 81
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 6
% 0.19/0.37  # Unit Clause-clause subsumption calls : 12
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 22
% 0.19/0.37  # BW rewrite match successes           : 14
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 8053
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.034 s
% 0.19/0.37  # System time              : 0.006 s
% 0.19/0.37  # Total time               : 0.041 s
% 0.19/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
