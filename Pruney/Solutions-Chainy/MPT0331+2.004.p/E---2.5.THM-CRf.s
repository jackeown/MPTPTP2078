%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:31 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 951 expanded)
%              Number of clauses        :   40 ( 458 expanded)
%              Number of leaves         :   14 ( 245 expanded)
%              Depth                    :   15
%              Number of atoms          :  110 (1621 expanded)
%              Number of equality atoms :   59 ( 740 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(l36_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t144_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3)
        & X3 != k4_xboole_0(X3,k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(t72_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(c_0_14,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_15,plain,(
    ! [X33,X34,X35] :
      ( ( r2_hidden(X33,X34)
        | ~ r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))) )
      & ( X33 != X35
        | ~ r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))) )
      & ( ~ r2_hidden(X33,X34)
        | X33 = X35
        | r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_16,plain,(
    ! [X32] : k2_tarski(X32,X32) = k1_tarski(X32) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_17,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k2_xboole_0(X15,X16) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X26,X27,X28] : k3_xboole_0(X26,k4_xboole_0(X27,X28)) = k4_xboole_0(k3_xboole_0(X26,X27),X28) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_23,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k4_xboole_0(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_24,plain,(
    ! [X29,X30,X31] : k4_xboole_0(X29,k4_xboole_0(X30,X31)) = k2_xboole_0(k4_xboole_0(X29,X30),k3_xboole_0(X29,X31)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

fof(c_0_25,plain,(
    ! [X21,X22,X23] : k4_xboole_0(k4_xboole_0(X21,X22),X23) = k4_xboole_0(X21,k2_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_28,plain,(
    ! [X17,X18] : k2_xboole_0(X17,k3_xboole_0(X17,X18)) = X17 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_29,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k2_tarski(X2,X2))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X1,X1))) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_31])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_31])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_35,c_0_31])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k2_tarski(X1,X1))))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_42])).

fof(c_0_45,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_46,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_19])).

fof(c_0_47,plain,(
    ! [X12,X13,X14] : k4_xboole_0(X12,k3_xboole_0(X13,X14)) = k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,X14)) ),
    inference(variable_rename,[status(thm)],[l36_xboole_1])).

fof(c_0_48,plain,(
    ! [X19,X20] : k2_xboole_0(X19,k4_xboole_0(X20,X19)) = k2_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X1),X2) = X2 ),
    inference(spm,[status(thm)],[c_0_26,c_0_46])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_31])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_50]),c_0_50])).

fof(c_0_56,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( ~ r2_hidden(X1,X3)
          & ~ r2_hidden(X2,X3)
          & X3 != k4_xboole_0(X3,k2_tarski(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t144_zfmisc_1])).

cnf(c_0_57,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X3)) = k4_xboole_0(X1,k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_38])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_53])).

cnf(c_0_59,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_55]),c_0_55]),c_0_49])).

fof(c_0_60,plain,(
    ! [X38,X39,X40] :
      ( ( ~ r2_hidden(X38,X40)
        | k4_xboole_0(k2_tarski(X38,X39),X40) != k2_tarski(X38,X39) )
      & ( ~ r2_hidden(X39,X40)
        | k4_xboole_0(k2_tarski(X38,X39),X40) != k2_tarski(X38,X39) )
      & ( r2_hidden(X38,X40)
        | r2_hidden(X39,X40)
        | k4_xboole_0(k2_tarski(X38,X39),X40) = k2_tarski(X38,X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).

fof(c_0_61,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk4_0)
    & ~ r2_hidden(esk3_0,esk4_0)
    & esk4_0 != k4_xboole_0(esk4_0,k2_tarski(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_56])])])])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_55]),c_0_59])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | k4_xboole_0(k2_tarski(X1,X3),X2) = k2_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( esk4_0 != k4_xboole_0(esk4_0,k2_tarski(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,k2_tarski(X2,X3)) = X1
    | r2_hidden(X2,X1)
    | r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_67]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.75/1.93  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4b
% 1.75/1.93  # and selection function SelectCQIPrecW.
% 1.75/1.93  #
% 1.75/1.93  # Preprocessing time       : 0.027 s
% 1.75/1.93  # Presaturation interreduction done
% 1.75/1.93  
% 1.75/1.93  # Proof found!
% 1.75/1.93  # SZS status Theorem
% 1.75/1.93  # SZS output start CNFRefutation
% 1.75/1.93  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.75/1.93  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 1.75/1.93  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.75/1.93  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.75/1.93  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 1.75/1.93  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.75/1.93  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 1.75/1.93  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.75/1.93  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 1.75/1.93  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.75/1.93  fof(l36_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l36_xboole_1)).
% 1.75/1.93  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.75/1.93  fof(t144_zfmisc_1, conjecture, ![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(X3,k2_tarski(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 1.75/1.93  fof(t72_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 1.75/1.93  fof(c_0_14, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.75/1.93  fof(c_0_15, plain, ![X33, X34, X35]:(((r2_hidden(X33,X34)|~r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))))&(X33!=X35|~r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35)))))&(~r2_hidden(X33,X34)|X33=X35|r2_hidden(X33,k4_xboole_0(X34,k1_tarski(X35))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 1.75/1.93  fof(c_0_16, plain, ![X32]:k2_tarski(X32,X32)=k1_tarski(X32), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.75/1.93  fof(c_0_17, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k2_xboole_0(X15,X16)=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 1.75/1.93  cnf(c_0_18, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.75/1.93  cnf(c_0_19, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.75/1.93  cnf(c_0_20, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.75/1.93  cnf(c_0_21, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.75/1.93  fof(c_0_22, plain, ![X26, X27, X28]:k3_xboole_0(X26,k4_xboole_0(X27,X28))=k4_xboole_0(k3_xboole_0(X26,X27),X28), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 1.75/1.93  fof(c_0_23, plain, ![X24, X25]:k4_xboole_0(X24,k4_xboole_0(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.75/1.93  fof(c_0_24, plain, ![X29, X30, X31]:k4_xboole_0(X29,k4_xboole_0(X30,X31))=k2_xboole_0(k4_xboole_0(X29,X30),k3_xboole_0(X29,X31)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 1.75/1.93  fof(c_0_25, plain, ![X21, X22, X23]:k4_xboole_0(k4_xboole_0(X21,X22),X23)=k4_xboole_0(X21,k2_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 1.75/1.93  cnf(c_0_26, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.75/1.93  cnf(c_0_27, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 1.75/1.93  fof(c_0_28, plain, ![X17, X18]:k2_xboole_0(X17,k3_xboole_0(X17,X18))=X17, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 1.75/1.93  cnf(c_0_29, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k2_tarski(X2,X2)))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 1.75/1.93  cnf(c_0_30, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.75/1.93  cnf(c_0_31, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.75/1.93  cnf(c_0_32, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.75/1.93  cnf(c_0_33, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.75/1.93  cnf(c_0_34, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 1.75/1.93  cnf(c_0_35, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.75/1.93  cnf(c_0_36, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X1,X1)))), inference(er,[status(thm)],[c_0_29])).
% 1.75/1.93  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_31])).
% 1.75/1.93  cnf(c_0_38, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[c_0_32, c_0_31])).
% 1.75/1.93  cnf(c_0_39, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.75/1.93  cnf(c_0_40, plain, (k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_35, c_0_31])).
% 1.75/1.93  cnf(c_0_41, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k2_tarski(X1,X1)))))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 1.75/1.93  cnf(c_0_42, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 1.75/1.93  cnf(c_0_43, plain, (~r2_hidden(X1,k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.75/1.93  cnf(c_0_44, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_43, c_0_42])).
% 1.75/1.93  fof(c_0_45, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 1.75/1.93  cnf(c_0_46, plain, (r1_tarski(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_44, c_0_19])).
% 1.75/1.93  fof(c_0_47, plain, ![X12, X13, X14]:k4_xboole_0(X12,k3_xboole_0(X13,X14))=k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X12,X14)), inference(variable_rename,[status(thm)],[l36_xboole_1])).
% 1.75/1.93  fof(c_0_48, plain, ![X19, X20]:k2_xboole_0(X19,k4_xboole_0(X20,X19))=k2_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 1.75/1.93  cnf(c_0_49, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.75/1.93  cnf(c_0_50, plain, (k2_xboole_0(k4_xboole_0(X1,X1),X2)=X2), inference(spm,[status(thm)],[c_0_26, c_0_46])).
% 1.75/1.93  cnf(c_0_51, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.75/1.93  cnf(c_0_52, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.75/1.93  cnf(c_0_53, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 1.75/1.93  cnf(c_0_54, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(rw,[status(thm)],[c_0_51, c_0_31])).
% 1.75/1.93  cnf(c_0_55, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_50]), c_0_50])).
% 1.75/1.93  fof(c_0_56, negated_conjecture, ~(![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(X3,k2_tarski(X1,X2))))), inference(assume_negation,[status(cth)],[t144_zfmisc_1])).
% 1.75/1.93  cnf(c_0_57, plain, (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X3))=k4_xboole_0(X1,k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_49, c_0_38])).
% 1.75/1.93  cnf(c_0_58, plain, (k4_xboole_0(X1,X1)=k4_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_50, c_0_53])).
% 1.75/1.93  cnf(c_0_59, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_55]), c_0_55]), c_0_49])).
% 1.75/1.93  fof(c_0_60, plain, ![X38, X39, X40]:(((~r2_hidden(X38,X40)|k4_xboole_0(k2_tarski(X38,X39),X40)!=k2_tarski(X38,X39))&(~r2_hidden(X39,X40)|k4_xboole_0(k2_tarski(X38,X39),X40)!=k2_tarski(X38,X39)))&(r2_hidden(X38,X40)|r2_hidden(X39,X40)|k4_xboole_0(k2_tarski(X38,X39),X40)=k2_tarski(X38,X39))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).
% 1.75/1.93  fof(c_0_61, negated_conjecture, ((~r2_hidden(esk2_0,esk4_0)&~r2_hidden(esk3_0,esk4_0))&esk4_0!=k4_xboole_0(esk4_0,k2_tarski(esk2_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_56])])])])).
% 1.75/1.93  cnf(c_0_62, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_55]), c_0_59])).
% 1.75/1.93  cnf(c_0_63, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|k4_xboole_0(k2_tarski(X1,X3),X2)=k2_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 1.75/1.93  cnf(c_0_64, negated_conjecture, (esk4_0!=k4_xboole_0(esk4_0,k2_tarski(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 1.75/1.93  cnf(c_0_65, plain, (k4_xboole_0(X1,k2_tarski(X2,X3))=X1|r2_hidden(X2,X1)|r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 1.75/1.93  cnf(c_0_66, negated_conjecture, (~r2_hidden(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 1.75/1.93  cnf(c_0_67, negated_conjecture, (~r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 1.75/1.93  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_67]), ['proof']).
% 1.75/1.93  # SZS output end CNFRefutation
% 1.75/1.93  # Proof object total steps             : 69
% 1.75/1.93  # Proof object clause steps            : 40
% 1.75/1.93  # Proof object formula steps           : 29
% 1.75/1.93  # Proof object conjectures             : 7
% 1.75/1.93  # Proof object clause conjectures      : 4
% 1.75/1.93  # Proof object formula conjectures     : 3
% 1.75/1.93  # Proof object initial clauses used    : 17
% 1.75/1.93  # Proof object initial formulas used   : 14
% 1.75/1.93  # Proof object generating inferences   : 17
% 1.75/1.93  # Proof object simplifying inferences  : 16
% 1.75/1.93  # Training examples: 0 positive, 0 negative
% 1.75/1.93  # Parsed axioms                        : 15
% 1.75/1.93  # Removed by relevancy pruning/SinE    : 0
% 1.75/1.93  # Initial clauses                      : 24
% 1.75/1.93  # Removed in clause preprocessing      : 2
% 1.75/1.93  # Initial clauses in saturation        : 22
% 1.75/1.93  # Processed clauses                    : 8344
% 1.75/1.93  # ...of these trivial                  : 330
% 1.75/1.93  # ...subsumed                          : 7408
% 1.75/1.93  # ...remaining for further processing  : 606
% 1.75/1.93  # Other redundant clauses eliminated   : 1
% 1.75/1.93  # Clauses deleted for lack of memory   : 0
% 1.75/1.93  # Backward-subsumed                    : 21
% 1.75/1.93  # Backward-rewritten                   : 62
% 1.75/1.93  # Generated clauses                    : 167192
% 1.75/1.93  # ...of the previous two non-trivial   : 141197
% 1.75/1.93  # Contextual simplify-reflections      : 0
% 1.75/1.93  # Paramodulations                      : 167152
% 1.75/1.93  # Factorizations                       : 36
% 1.75/1.93  # Equation resolutions                 : 4
% 1.75/1.93  # Propositional unsat checks           : 0
% 1.75/1.93  #    Propositional check models        : 0
% 1.75/1.93  #    Propositional check unsatisfiable : 0
% 1.75/1.93  #    Propositional clauses             : 0
% 1.75/1.93  #    Propositional clauses after purity: 0
% 1.75/1.93  #    Propositional unsat core size     : 0
% 1.75/1.93  #    Propositional preprocessing time  : 0.000
% 1.75/1.93  #    Propositional encoding time       : 0.000
% 1.75/1.93  #    Propositional solver time         : 0.000
% 1.75/1.93  #    Success case prop preproc time    : 0.000
% 1.75/1.93  #    Success case prop encoding time   : 0.000
% 1.75/1.93  #    Success case prop solver time     : 0.000
% 1.75/1.93  # Current number of processed clauses  : 500
% 1.75/1.93  #    Positive orientable unit clauses  : 147
% 1.75/1.93  #    Positive unorientable unit clauses: 26
% 1.75/1.93  #    Negative unit clauses             : 44
% 1.75/1.93  #    Non-unit-clauses                  : 283
% 1.75/1.93  # Current number of unprocessed clauses: 131464
% 1.75/1.93  # ...number of literals in the above   : 245423
% 1.75/1.93  # Current number of archived formulas  : 0
% 1.75/1.93  # Current number of archived clauses   : 107
% 1.75/1.93  # Clause-clause subsumption calls (NU) : 21239
% 1.75/1.93  # Rec. Clause-clause subsumption calls : 17076
% 1.75/1.93  # Non-unit clause-clause subsumptions  : 2668
% 1.75/1.93  # Unit Clause-clause subsumption calls : 1408
% 1.75/1.93  # Rewrite failures with RHS unbound    : 142
% 1.75/1.93  # BW rewrite match attempts            : 3579
% 1.75/1.93  # BW rewrite match successes           : 253
% 1.75/1.93  # Condensation attempts                : 0
% 1.75/1.93  # Condensation successes               : 0
% 1.75/1.93  # Termbank termtop insertions          : 3057876
% 1.75/1.94  
% 1.75/1.94  # -------------------------------------------------
% 1.75/1.94  # User time                : 1.489 s
% 1.75/1.94  # System time              : 0.101 s
% 1.75/1.94  # Total time               : 1.589 s
% 1.75/1.94  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
