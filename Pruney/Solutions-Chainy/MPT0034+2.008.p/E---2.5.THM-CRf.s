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
% DateTime   : Thu Dec  3 10:31:57 EST 2020

% Result     : Theorem 45.36s
% Output     : CNFRefutation 45.45s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 273 expanded)
%              Number of clauses        :   45 ( 129 expanded)
%              Number of leaves         :   10 (  69 expanded)
%              Depth                    :   12
%              Number of atoms          :  146 ( 544 expanded)
%              Number of equality atoms :   12 (  67 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t9_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t27_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t26_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).

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

fof(c_0_10,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(k2_xboole_0(X5,X6),X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_11,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_12,plain,(
    ! [X28,X29,X30] :
      ( ~ r1_tarski(X28,X29)
      | r1_tarski(k2_xboole_0(X28,X30),k2_xboole_0(X29,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_tarski(X12,X14)
      | r1_tarski(X12,k3_xboole_0(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X4) )
       => r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)) ) ),
    inference(assume_negation,[status(cth)],[t27_xboole_1])).

cnf(c_0_17,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X25] : r1_tarski(k1_xboole_0,X25) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_19,plain,(
    ! [X10,X11] : r1_tarski(k3_xboole_0(X10,X11),X10) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0)
    & r1_tarski(esk4_0,esk5_0)
    & ~ r1_tarski(k3_xboole_0(esk2_0,esk4_0),k3_xboole_0(esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1))
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_14])).

cnf(c_0_24,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3)
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X26,X27] : r1_tarski(X26,k2_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_24])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk4_0,k3_xboole_0(X1,X2))
    | ~ r1_tarski(esk5_0,X2)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_34,plain,(
    ! [X22,X23,X24] :
      ( ~ r1_tarski(X22,X23)
      | r1_tarski(k3_xboole_0(X22,X24),k3_xboole_0(X23,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_xboole_1])])).

cnf(c_0_35,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_14])).

fof(c_0_36,plain,(
    ! [X18,X19,X20] :
      ( ( r1_tarski(esk1_3(X18,X19,X20),X19)
        | ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X18,X20)
        | X18 = k3_xboole_0(X19,X20) )
      & ( r1_tarski(esk1_3(X18,X19,X20),X20)
        | ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X18,X20)
        | X18 = k3_xboole_0(X19,X20) )
      & ( ~ r1_tarski(esk1_3(X18,X19,X20),X18)
        | ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X18,X20)
        | X18 = k3_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_xboole_1])])])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_tarski(esk5_0,X2)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_33])).

cnf(c_0_41,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk2_0,X1),X1)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_33])).

cnf(c_0_43,plain,
    ( r1_tarski(esk1_3(X1,X2,X3),X3)
    | X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(esk2_0,esk4_0),k3_xboole_0(esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_40])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,k3_xboole_0(X4,X3))
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_42])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r1_tarski(esk1_3(X2,X1,X2),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk4_0,k2_xboole_0(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_32])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(esk2_0,esk4_0),esk5_0)
    | ~ r1_tarski(k3_xboole_0(esk2_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_21])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(X1,esk5_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_27])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,k3_xboole_0(esk2_0,X2)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_25])).

cnf(c_0_55,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))
    | ~ r1_tarski(X4,X3)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_48,c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_29])).

cnf(c_0_57,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(esk1_3(X1,X2,X3),X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_58,negated_conjecture,
    ( k3_xboole_0(k2_xboole_0(esk5_0,X1),esk4_0) = esk4_0
    | r1_tarski(esk1_3(esk4_0,k2_xboole_0(esk5_0,X1),esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(esk2_0,esk4_0),esk3_0)
    | ~ r1_tarski(k3_xboole_0(esk2_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_44])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X3,esk3_0),X2))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( k3_xboole_0(k2_xboole_0(esk5_0,X1),esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_44]),c_0_51])])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(esk2_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk4_0),esk4_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_44])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:04:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 45.36/45.62  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 45.36/45.62  # and selection function PSelectComplexExceptUniqMaxHorn.
% 45.36/45.62  #
% 45.36/45.62  # Preprocessing time       : 0.027 s
% 45.36/45.62  # Presaturation interreduction done
% 45.36/45.62  
% 45.36/45.62  # Proof found!
% 45.36/45.62  # SZS status Theorem
% 45.36/45.62  # SZS output start CNFRefutation
% 45.36/45.62  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 45.36/45.62  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 45.36/45.62  fof(t9_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_xboole_1)).
% 45.36/45.62  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 45.36/45.62  fof(t27_xboole_1, conjecture, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_xboole_1)).
% 45.36/45.62  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 45.36/45.62  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 45.36/45.62  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 45.36/45.62  fof(t26_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_xboole_1)).
% 45.36/45.62  fof(t20_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&![X4]:((r1_tarski(X4,X2)&r1_tarski(X4,X3))=>r1_tarski(X4,X1)))=>X1=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_xboole_1)).
% 45.36/45.62  fof(c_0_10, plain, ![X5, X6, X7]:(~r1_tarski(k2_xboole_0(X5,X6),X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 45.36/45.62  fof(c_0_11, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 45.36/45.62  fof(c_0_12, plain, ![X28, X29, X30]:(~r1_tarski(X28,X29)|r1_tarski(k2_xboole_0(X28,X30),k2_xboole_0(X29,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).
% 45.36/45.62  cnf(c_0_13, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 45.36/45.62  cnf(c_0_14, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 45.36/45.62  fof(c_0_15, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_tarski(X12,X14)|r1_tarski(X12,k3_xboole_0(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 45.36/45.62  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))), inference(assume_negation,[status(cth)],[t27_xboole_1])).
% 45.45/45.62  cnf(c_0_17, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 45.45/45.62  fof(c_0_18, plain, ![X25]:r1_tarski(k1_xboole_0,X25), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 45.45/45.62  fof(c_0_19, plain, ![X10, X11]:r1_tarski(k3_xboole_0(X10,X11),X10), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 45.45/45.62  cnf(c_0_20, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 45.45/45.62  cnf(c_0_21, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 45.45/45.62  fof(c_0_22, negated_conjecture, ((r1_tarski(esk2_0,esk3_0)&r1_tarski(esk4_0,esk5_0))&~r1_tarski(k3_xboole_0(esk2_0,esk4_0),k3_xboole_0(esk3_0,esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 45.45/45.62  cnf(c_0_23, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))|~r1_tarski(X3,X2)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_17, c_0_14])).
% 45.45/45.62  cnf(c_0_24, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 45.45/45.62  cnf(c_0_25, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 45.45/45.62  cnf(c_0_26, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X4)|~r1_tarski(X4,X3)|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 45.45/45.62  cnf(c_0_27, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 45.45/45.62  fof(c_0_28, plain, ![X26, X27]:r1_tarski(X26,k2_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 45.45/45.62  cnf(c_0_29, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_24])])).
% 45.45/45.62  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_20, c_0_25])).
% 45.45/45.62  cnf(c_0_31, negated_conjecture, (r1_tarski(esk4_0,k3_xboole_0(X1,X2))|~r1_tarski(esk5_0,X2)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 45.45/45.62  cnf(c_0_32, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 45.45/45.62  cnf(c_0_33, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 45.45/45.62  fof(c_0_34, plain, ![X22, X23, X24]:(~r1_tarski(X22,X23)|r1_tarski(k3_xboole_0(X22,X24),k3_xboole_0(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_xboole_1])])).
% 45.45/45.62  cnf(c_0_35, plain, (r1_tarski(k2_xboole_0(X1,X2),X2)|~r1_tarski(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_17, c_0_14])).
% 45.45/45.62  fof(c_0_36, plain, ![X18, X19, X20]:(((r1_tarski(esk1_3(X18,X19,X20),X19)|(~r1_tarski(X18,X19)|~r1_tarski(X18,X20))|X18=k3_xboole_0(X19,X20))&(r1_tarski(esk1_3(X18,X19,X20),X20)|(~r1_tarski(X18,X19)|~r1_tarski(X18,X20))|X18=k3_xboole_0(X19,X20)))&(~r1_tarski(esk1_3(X18,X19,X20),X18)|(~r1_tarski(X18,X19)|~r1_tarski(X18,X20))|X18=k3_xboole_0(X19,X20))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_xboole_1])])])])).
% 45.45/45.62  cnf(c_0_37, plain, (r1_tarski(X1,X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_29, c_0_14])).
% 45.45/45.62  cnf(c_0_38, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_tarski(esk5_0,X2)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 45.45/45.62  cnf(c_0_39, plain, (r1_tarski(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3))), inference(spm,[status(thm)],[c_0_13, c_0_32])).
% 45.45/45.62  cnf(c_0_40, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_20, c_0_33])).
% 45.45/45.62  cnf(c_0_41, plain, (r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 45.45/45.62  cnf(c_0_42, negated_conjecture, (r1_tarski(k2_xboole_0(esk2_0,X1),X1)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_35, c_0_33])).
% 45.45/45.62  cnf(c_0_43, plain, (r1_tarski(esk1_3(X1,X2,X3),X3)|X1=k3_xboole_0(X2,X3)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 45.45/45.62  cnf(c_0_44, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_37, c_0_24])).
% 45.45/45.62  cnf(c_0_45, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 45.45/45.62  cnf(c_0_46, negated_conjecture, (~r1_tarski(k3_xboole_0(esk2_0,esk4_0),k3_xboole_0(esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 45.45/45.62  cnf(c_0_47, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_40])).
% 45.45/45.62  cnf(c_0_48, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,k3_xboole_0(X4,X3))|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_20, c_0_41])).
% 45.45/45.62  cnf(c_0_49, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_13, c_0_42])).
% 45.45/45.62  cnf(c_0_50, plain, (k3_xboole_0(X1,X2)=X2|r1_tarski(esk1_3(X2,X1,X2),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 45.45/45.62  cnf(c_0_51, negated_conjecture, (r1_tarski(esk4_0,k2_xboole_0(esk5_0,X1))), inference(spm,[status(thm)],[c_0_45, c_0_32])).
% 45.45/45.62  cnf(c_0_52, negated_conjecture, (~r1_tarski(k3_xboole_0(esk2_0,esk4_0),esk5_0)|~r1_tarski(k3_xboole_0(esk2_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_46, c_0_21])).
% 45.45/45.62  cnf(c_0_53, negated_conjecture, (r1_tarski(X1,esk5_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_27])).
% 45.45/45.62  cnf(c_0_54, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,k3_xboole_0(esk2_0,X2))), inference(spm,[status(thm)],[c_0_47, c_0_25])).
% 45.45/45.62  cnf(c_0_55, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))|~r1_tarski(X4,X3)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_48, c_0_41])).
% 45.45/45.62  cnf(c_0_56, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(X1,esk3_0))), inference(spm,[status(thm)],[c_0_49, c_0_29])).
% 45.45/45.62  cnf(c_0_57, plain, (X1=k3_xboole_0(X2,X3)|~r1_tarski(esk1_3(X1,X2,X3),X1)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 45.45/45.62  cnf(c_0_58, negated_conjecture, (k3_xboole_0(k2_xboole_0(esk5_0,X1),esk4_0)=esk4_0|r1_tarski(esk1_3(esk4_0,k2_xboole_0(esk5_0,X1),esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 45.45/45.62  cnf(c_0_59, negated_conjecture, (~r1_tarski(k3_xboole_0(esk2_0,esk4_0),esk3_0)|~r1_tarski(k3_xboole_0(esk2_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 45.45/45.62  cnf(c_0_60, negated_conjecture, (r1_tarski(k3_xboole_0(esk2_0,X1),esk3_0)), inference(spm,[status(thm)],[c_0_54, c_0_44])).
% 45.45/45.62  cnf(c_0_61, negated_conjecture, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X3,esk3_0),X2))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 45.45/45.62  cnf(c_0_62, negated_conjecture, (k3_xboole_0(k2_xboole_0(esk5_0,X1),esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_44]), c_0_51])])).
% 45.45/45.62  cnf(c_0_63, negated_conjecture, (~r1_tarski(k3_xboole_0(esk2_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60])])).
% 45.45/45.62  cnf(c_0_64, negated_conjecture, (r1_tarski(k3_xboole_0(X1,esk4_0),esk4_0)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 45.45/45.62  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_44])]), ['proof']).
% 45.45/45.62  # SZS output end CNFRefutation
% 45.45/45.62  # Proof object total steps             : 66
% 45.45/45.62  # Proof object clause steps            : 45
% 45.45/45.62  # Proof object formula steps           : 21
% 45.45/45.62  # Proof object conjectures             : 26
% 45.45/45.62  # Proof object clause conjectures      : 23
% 45.45/45.62  # Proof object formula conjectures     : 3
% 45.45/45.62  # Proof object initial clauses used    : 13
% 45.45/45.62  # Proof object initial formulas used   : 10
% 45.45/45.62  # Proof object generating inferences   : 31
% 45.45/45.62  # Proof object simplifying inferences  : 9
% 45.45/45.62  # Training examples: 0 positive, 0 negative
% 45.45/45.62  # Parsed axioms                        : 11
% 45.45/45.62  # Removed by relevancy pruning/SinE    : 0
% 45.45/45.62  # Initial clauses                      : 15
% 45.45/45.62  # Removed in clause preprocessing      : 0
% 45.45/45.62  # Initial clauses in saturation        : 15
% 45.45/45.62  # Processed clauses                    : 110733
% 45.45/45.62  # ...of these trivial                  : 263
% 45.45/45.62  # ...subsumed                          : 100655
% 45.45/45.62  # ...remaining for further processing  : 9815
% 45.45/45.62  # Other redundant clauses eliminated   : 0
% 45.45/45.62  # Clauses deleted for lack of memory   : 400835
% 45.45/45.62  # Backward-subsumed                    : 440
% 45.45/45.62  # Backward-rewritten                   : 1177
% 45.45/45.62  # Generated clauses                    : 3592547
% 45.45/45.62  # ...of the previous two non-trivial   : 3497452
% 45.45/45.62  # Contextual simplify-reflections      : 142
% 45.45/45.62  # Paramodulations                      : 3592547
% 45.45/45.62  # Factorizations                       : 0
% 45.45/45.62  # Equation resolutions                 : 0
% 45.45/45.62  # Propositional unsat checks           : 1
% 45.45/45.62  #    Propositional check models        : 0
% 45.45/45.62  #    Propositional check unsatisfiable : 0
% 45.45/45.62  #    Propositional clauses             : 0
% 45.45/45.62  #    Propositional clauses after purity: 0
% 45.45/45.62  #    Propositional unsat core size     : 0
% 45.45/45.62  #    Propositional preprocessing time  : 0.000
% 45.45/45.62  #    Propositional encoding time       : 1.439
% 45.45/45.62  #    Propositional solver time         : 0.565
% 45.45/45.62  #    Success case prop preproc time    : 0.000
% 45.45/45.62  #    Success case prop encoding time   : 0.000
% 45.45/45.62  #    Success case prop solver time     : 0.000
% 45.45/45.62  # Current number of processed clauses  : 8183
% 45.45/45.62  #    Positive orientable unit clauses  : 175
% 45.45/45.62  #    Positive unorientable unit clauses: 0
% 45.45/45.62  #    Negative unit clauses             : 206
% 45.45/45.62  #    Non-unit-clauses                  : 7802
% 45.45/45.62  # Current number of unprocessed clauses: 1266700
% 45.45/45.62  # ...number of literals in the above   : 4971542
% 45.45/45.62  # Current number of archived formulas  : 0
% 45.45/45.62  # Current number of archived clauses   : 1632
% 45.45/45.62  # Clause-clause subsumption calls (NU) : 6188049
% 45.45/45.62  # Rec. Clause-clause subsumption calls : 2883970
% 45.45/45.62  # Non-unit clause-clause subsumptions  : 44987
% 45.45/45.62  # Unit Clause-clause subsumption calls : 84384
% 45.45/45.62  # Rewrite failures with RHS unbound    : 0
% 45.45/45.62  # BW rewrite match attempts            : 4084
% 45.45/45.62  # BW rewrite match successes           : 135
% 45.45/45.62  # Condensation attempts                : 0
% 45.45/45.62  # Condensation successes               : 0
% 45.45/45.62  # Termbank termtop insertions          : 101930451
% 45.52/45.69  
% 45.52/45.69  # -------------------------------------------------
% 45.52/45.69  # User time                : 44.239 s
% 45.52/45.69  # System time              : 1.110 s
% 45.52/45.69  # Total time               : 45.349 s
% 45.52/45.69  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
