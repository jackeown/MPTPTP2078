%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:59 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 (1570 expanded)
%              Number of clauses        :   72 ( 726 expanded)
%              Number of leaves         :   13 ( 402 expanded)
%              Depth                    :   16
%              Number of atoms          :  172 (3095 expanded)
%              Number of equality atoms :   56 (1295 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t71_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X2)
        & r1_xboole_0(X1,X2)
        & r1_xboole_0(X3,X2) )
     => X1 = X3 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t64_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4)
        & r1_xboole_0(X2,X4) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(c_0_13,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( r1_xboole_0(X15,X16)
        | r2_hidden(esk2_2(X15,X16),k3_xboole_0(X15,X16)) )
      & ( ~ r2_hidden(X20,k3_xboole_0(X18,X19))
        | ~ r1_xboole_0(X18,X19) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_14,plain,(
    ! [X28,X29] : k4_xboole_0(X28,k4_xboole_0(X28,X29)) = k3_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_xboole_0(X9,X10) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | r1_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X2)
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X3,X2) )
       => X1 = X3 ) ),
    inference(assume_negation,[status(cth)],[t71_xboole_1])).

cnf(c_0_19,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk4_0)
    & r1_xboole_0(esk3_0,esk4_0)
    & r1_xboole_0(esk5_0,esk4_0)
    & esk3_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_22,plain,(
    ! [X26,X27] : k4_xboole_0(X26,k3_xboole_0(X26,X27)) = k4_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_23,plain,(
    ! [X37] :
      ( ( r1_xboole_0(X37,X37)
        | X37 != k1_xboole_0 )
      & ( X37 = k1_xboole_0
        | ~ r1_xboole_0(X37,X37) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_29,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_30,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_34,plain,(
    ! [X38,X39] : r1_tarski(X38,k2_xboole_0(X38,X39)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_35,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk4_0) = k4_xboole_0(esk5_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_16]),c_0_16])).

fof(c_0_38,plain,(
    ! [X33,X34,X35,X36] :
      ( ~ r1_tarski(X33,X34)
      | ~ r1_tarski(X35,X36)
      | ~ r1_xboole_0(X34,X36)
      | r1_xboole_0(X33,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_xboole_1])])).

fof(c_0_39,plain,(
    ! [X7,X8] :
      ( ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_40,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,k2_xboole_0(X24,X25))
      | r1_tarski(k4_xboole_0(X23,X24),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = k2_xboole_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,esk5_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_36]),c_0_37])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4)
    | ~ r1_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_28,c_0_32])).

fof(c_0_48,plain,(
    ! [X30,X31,X32] :
      ( ~ r1_tarski(X30,X31)
      | ~ r1_xboole_0(X31,X32)
      | r1_xboole_0(X30,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_49,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk5_0,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k4_xboole_0(esk3_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,esk5_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_44])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_37])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X3,k2_xboole_0(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_41])).

cnf(c_0_55,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk5_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_51]),c_0_37])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_37])).

cnf(c_0_60,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_52])).

fof(c_0_61,plain,(
    ! [X21,X22] :
      ( k4_xboole_0(X21,X22) != k4_xboole_0(X22,X21)
      | X21 = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).

cnf(c_0_62,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_37]),c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_41])).

cnf(c_0_65,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk5_0,esk3_0),X1)
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_25])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk5_0),esk4_0)
    | ~ r1_tarski(X1,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_42])).

cnf(c_0_68,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_69,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,esk3_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,esk4_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_36]),c_0_37]),c_0_52]),c_0_60]),c_0_37]),c_0_52]),c_0_60]),c_0_37])).

cnf(c_0_71,plain,
    ( X1 = X2
    | k4_xboole_0(X1,X2) != k4_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_72,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_37]),c_0_62])).

cnf(c_0_73,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_47])).

cnf(c_0_74,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_75,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_76,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk5_0,esk3_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_41])).

cnf(c_0_78,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_68,c_0_16])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk3_0) = k4_xboole_0(esk4_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_51]),c_0_37]),c_0_69]),c_0_60])).

cnf(c_0_80,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,esk4_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_70])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_60]),c_0_47])])).

cnf(c_0_82,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) != k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_31])).

cnf(c_0_83,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_73])).

cnf(c_0_84,negated_conjecture,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_74])).

cnf(c_0_85,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_75])).

cnf(c_0_86,negated_conjecture,
    ( r1_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_76])).

cnf(c_0_87,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk3_0,esk5_0),X1)
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_77])).

cnf(c_0_88,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_37]),c_0_80]),c_0_60]),c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( k4_xboole_0(X1,k1_xboole_0) = X1
    | k4_xboole_0(k4_xboole_0(X1,k1_xboole_0),X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_62])).

cnf(c_0_90,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_62,c_0_84])).

cnf(c_0_91,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk5_0,esk3_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_31])).

cnf(c_0_92,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk3_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90])])).

cnf(c_0_94,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( esk3_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_96,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk3_0,esk5_0),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_92]),c_0_90]),c_0_93])).

cnf(c_0_97,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk5_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_94]),c_0_95])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_96]),c_0_97]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:10:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___024_B31_F1_PI_AE_Q4_CS_SP_S2S
% 0.20/0.38  # and selection function SelectNewComplexAHP.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.025 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.38  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.38  fof(t71_xboole_1, conjecture, ![X1, X2, X3]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X2)&r1_xboole_0(X1,X2))&r1_xboole_0(X3,X2))=>X1=X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_xboole_1)).
% 0.20/0.38  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.20/0.38  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.20/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.38  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.38  fof(t64_xboole_1, axiom, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&r1_tarski(X3,X4))&r1_xboole_0(X2,X4))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_xboole_1)).
% 0.20/0.38  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.38  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.20/0.38  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.20/0.38  fof(t32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k4_xboole_0(X2,X1)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_xboole_1)).
% 0.20/0.38  fof(c_0_13, plain, ![X15, X16, X18, X19, X20]:((r1_xboole_0(X15,X16)|r2_hidden(esk2_2(X15,X16),k3_xboole_0(X15,X16)))&(~r2_hidden(X20,k3_xboole_0(X18,X19))|~r1_xboole_0(X18,X19))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.38  fof(c_0_14, plain, ![X28, X29]:k4_xboole_0(X28,k4_xboole_0(X28,X29))=k3_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.38  cnf(c_0_15, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_16, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  fof(c_0_17, plain, ![X9, X10, X12, X13, X14]:(((r2_hidden(esk1_2(X9,X10),X9)|r1_xboole_0(X9,X10))&(r2_hidden(esk1_2(X9,X10),X10)|r1_xboole_0(X9,X10)))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|~r1_xboole_0(X12,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.38  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X2)&r1_xboole_0(X1,X2))&r1_xboole_0(X3,X2))=>X1=X3)), inference(assume_negation,[status(cth)],[t71_xboole_1])).
% 0.20/0.38  cnf(c_0_19, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.38  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  fof(c_0_21, negated_conjecture, (((k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk4_0)&r1_xboole_0(esk3_0,esk4_0))&r1_xboole_0(esk5_0,esk4_0))&esk3_0!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.20/0.38  fof(c_0_22, plain, ![X26, X27]:k4_xboole_0(X26,k3_xboole_0(X26,X27))=k4_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.20/0.38  fof(c_0_23, plain, ![X37]:((r1_xboole_0(X37,X37)|X37!=k1_xboole_0)&(X37=k1_xboole_0|~r1_xboole_0(X37,X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.20/0.38  cnf(c_0_24, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (r1_xboole_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_26, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_27, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk4_0)))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.38  fof(c_0_29, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_31, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_16])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.38  cnf(c_0_33, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.38  fof(c_0_34, plain, ![X38, X39]:r1_tarski(X38,k2_xboole_0(X38,X39)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_24, c_0_30])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (k4_xboole_0(esk5_0,esk4_0)=k4_xboole_0(esk5_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.38  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_16]), c_0_16])).
% 0.20/0.38  fof(c_0_38, plain, ![X33, X34, X35, X36]:(~r1_tarski(X33,X34)|~r1_tarski(X35,X36)|~r1_xboole_0(X34,X36)|r1_xboole_0(X33,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_xboole_1])])).
% 0.20/0.38  fof(c_0_39, plain, ![X7, X8]:(~r1_xboole_0(X7,X8)|r1_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.38  fof(c_0_40, plain, ![X23, X24, X25]:(~r1_tarski(X23,k2_xboole_0(X24,X25))|r1_tarski(k4_xboole_0(X23,X24),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.20/0.38  cnf(c_0_41, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=k2_xboole_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_43, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_35])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,esk5_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_36]), c_0_37])).
% 0.20/0.38  cnf(c_0_45, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)|~r1_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.38  cnf(c_0_46, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (r1_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_28, c_0_32])).
% 0.20/0.38  fof(c_0_48, plain, ![X30, X31, X32]:(~r1_tarski(X30,X31)|~r1_xboole_0(X31,X32)|r1_xboole_0(X30,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.20/0.38  cnf(c_0_49, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (r1_tarski(esk5_0,k2_xboole_0(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k4_xboole_0(esk3_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_43])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (k4_xboole_0(k1_xboole_0,esk5_0)=k4_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_44])).
% 0.20/0.38  cnf(c_0_53, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_37])).
% 0.20/0.38  cnf(c_0_54, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X3,k2_xboole_0(X2,X4))), inference(spm,[status(thm)],[c_0_45, c_0_41])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.38  cnf(c_0_56, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, (r1_tarski(k4_xboole_0(esk5_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.38  cnf(c_0_58, negated_conjecture, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_51]), c_0_37])).
% 0.20/0.38  cnf(c_0_59, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_31, c_0_37])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_44, c_0_52])).
% 0.20/0.38  fof(c_0_61, plain, ![X21, X22]:(k4_xboole_0(X21,X22)!=k4_xboole_0(X22,X21)|X21=X22), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).
% 0.20/0.38  cnf(c_0_62, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k4_xboole_0(k4_xboole_0(X1,X2),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_37]), c_0_53])).
% 0.20/0.38  cnf(c_0_63, negated_conjecture, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.38  cnf(c_0_64, plain, (r1_tarski(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_49, c_0_41])).
% 0.20/0.38  cnf(c_0_65, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk5_0,esk3_0),X1)|~r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.38  cnf(c_0_66, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_46, c_0_25])).
% 0.20/0.38  cnf(c_0_67, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk5_0),esk4_0)|~r1_tarski(X1,k2_xboole_0(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_49, c_0_42])).
% 0.20/0.38  cnf(c_0_68, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_69, negated_conjecture, (k4_xboole_0(k1_xboole_0,esk3_0)=k4_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_58])).
% 0.20/0.38  cnf(c_0_70, negated_conjecture, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,esk4_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_36]), c_0_37]), c_0_52]), c_0_60]), c_0_37]), c_0_52]), c_0_60]), c_0_37])).
% 0.20/0.38  cnf(c_0_71, plain, (X1=X2|k4_xboole_0(X1,X2)!=k4_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.38  cnf(c_0_72, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X1)=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_37]), c_0_62])).
% 0.20/0.38  cnf(c_0_73, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_24, c_0_47])).
% 0.20/0.38  cnf(c_0_74, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.38  cnf(c_0_75, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_76, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk5_0,esk3_0),esk5_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.38  cnf(c_0_77, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_67, c_0_41])).
% 0.20/0.38  cnf(c_0_78, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_68, c_0_16])).
% 0.20/0.38  cnf(c_0_79, negated_conjecture, (k4_xboole_0(esk4_0,esk3_0)=k4_xboole_0(esk4_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_51]), c_0_37]), c_0_69]), c_0_60])).
% 0.20/0.38  cnf(c_0_80, negated_conjecture, (k4_xboole_0(k1_xboole_0,esk4_0)=k4_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_70])).
% 0.20/0.38  cnf(c_0_81, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_60]), c_0_47])])).
% 0.20/0.38  cnf(c_0_82, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)!=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_31])).
% 0.20/0.38  cnf(c_0_83, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_73])).
% 0.20/0.38  cnf(c_0_84, negated_conjecture, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_74])).
% 0.20/0.38  cnf(c_0_85, plain, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_19, c_0_75])).
% 0.20/0.38  cnf(c_0_86, negated_conjecture, (r1_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk3_0))), inference(spm,[status(thm)],[c_0_46, c_0_76])).
% 0.20/0.38  cnf(c_0_87, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk3_0,esk5_0),X1)|~r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_56, c_0_77])).
% 0.20/0.38  cnf(c_0_88, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_37]), c_0_80]), c_0_60]), c_0_81])).
% 0.20/0.38  cnf(c_0_89, negated_conjecture, (k4_xboole_0(X1,k1_xboole_0)=X1|k4_xboole_0(k4_xboole_0(X1,k1_xboole_0),X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_62])).
% 0.20/0.38  cnf(c_0_90, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_62, c_0_84])).
% 0.20/0.38  cnf(c_0_91, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk5_0,esk3_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_31])).
% 0.20/0.38  cnf(c_0_92, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk3_0,esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.20/0.38  cnf(c_0_93, negated_conjecture, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_90])])).
% 0.20/0.38  cnf(c_0_94, negated_conjecture, (k4_xboole_0(esk5_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_91])).
% 0.20/0.38  cnf(c_0_95, negated_conjecture, (esk3_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_96, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk3_0,esk5_0),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_92]), c_0_90]), c_0_93])).
% 0.20/0.38  cnf(c_0_97, negated_conjecture, (k4_xboole_0(esk3_0,esk5_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_94]), c_0_95])).
% 0.20/0.38  cnf(c_0_98, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_96]), c_0_97]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 99
% 0.20/0.38  # Proof object clause steps            : 72
% 0.20/0.38  # Proof object formula steps           : 27
% 0.20/0.38  # Proof object conjectures             : 47
% 0.20/0.38  # Proof object clause conjectures      : 44
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 18
% 0.20/0.38  # Proof object initial formulas used   : 13
% 0.20/0.38  # Proof object generating inferences   : 44
% 0.20/0.38  # Proof object simplifying inferences  : 39
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 13
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 20
% 0.20/0.38  # Removed in clause preprocessing      : 1
% 0.20/0.38  # Initial clauses in saturation        : 19
% 0.20/0.38  # Processed clauses                    : 299
% 0.20/0.38  # ...of these trivial                  : 29
% 0.20/0.38  # ...subsumed                          : 144
% 0.20/0.38  # ...remaining for further processing  : 126
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 1
% 0.20/0.38  # Backward-rewritten                   : 48
% 0.20/0.38  # Generated clauses                    : 1172
% 0.20/0.38  # ...of the previous two non-trivial   : 697
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 1170
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 2
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 77
% 0.20/0.38  #    Positive orientable unit clauses  : 26
% 0.20/0.38  #    Positive unorientable unit clauses: 1
% 0.20/0.38  #    Negative unit clauses             : 3
% 0.20/0.38  #    Non-unit-clauses                  : 47
% 0.20/0.38  # Current number of unprocessed clauses: 316
% 0.20/0.38  # ...number of literals in the above   : 589
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 50
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 552
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 528
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 97
% 0.20/0.38  # Unit Clause-clause subsumption calls : 31
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 78
% 0.20/0.38  # BW rewrite match successes           : 40
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 12882
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.037 s
% 0.20/0.38  # System time              : 0.005 s
% 0.20/0.38  # Total time               : 0.042 s
% 0.20/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
