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
% DateTime   : Thu Dec  3 10:34:35 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 415 expanded)
%              Number of clauses        :   50 ( 192 expanded)
%              Number of leaves         :   15 ( 110 expanded)
%              Depth                    :   15
%              Number of atoms          :  122 ( 540 expanded)
%              Number of equality atoms :   44 ( 335 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t106_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(c_0_15,plain,(
    ! [X27,X28] : r1_tarski(k4_xboole_0(X27,X28),X27) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_16,plain,(
    ! [X19,X20] : k4_xboole_0(X19,X20) = k5_xboole_0(X19,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_17,plain,(
    ! [X32,X33] : k4_xboole_0(X32,k4_xboole_0(X32,X33)) = k3_xboole_0(X32,X33) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_18,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_19,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_20,plain,(
    ! [X38,X39] : r1_xboole_0(k4_xboole_0(X38,X39),X39) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_21,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X10] : k3_xboole_0(X10,X10) = X10 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_28,plain,(
    ! [X31] : k4_xboole_0(X31,k1_xboole_0) = X31 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_29,plain,(
    ! [X25,X26] :
      ( ~ r1_tarski(X25,X26)
      | k3_xboole_0(X25,X26) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_22]),c_0_22])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_22])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X29,X30] : k2_xboole_0(X29,k4_xboole_0(X30,X29)) = k2_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( r1_xboole_0(k5_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_36,c_0_22])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_25])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,X1) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_42]),c_0_35])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_43,c_0_22])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_44])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_50,plain,(
    ! [X24] : k2_xboole_0(X24,k1_xboole_0) = X24 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_51,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k4_xboole_0(X2,X3))
       => ( r1_tarski(X1,X2)
          & r1_xboole_0(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t106_xboole_1])).

fof(c_0_52,plain,(
    ! [X35,X36,X37] :
      ( ( r1_xboole_0(X35,k2_xboole_0(X36,X37))
        | ~ r1_xboole_0(X35,X36)
        | ~ r1_xboole_0(X35,X37) )
      & ( r1_xboole_0(X35,X36)
        | ~ r1_xboole_0(X35,k2_xboole_0(X36,X37)) )
      & ( r1_xboole_0(X35,X37)
        | ~ r1_xboole_0(X35,k2_xboole_0(X36,X37)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_25])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_56,negated_conjecture,
    ( r1_tarski(esk3_0,k4_xboole_0(esk4_0,esk5_0))
    & ( ~ r1_tarski(esk3_0,esk4_0)
      | ~ r1_xboole_0(esk3_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_51])])])).

cnf(c_0_57,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_44]),c_0_46]),c_0_54]),c_0_55])).

cnf(c_0_59,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_25])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk3_0,k4_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_61,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(k2_xboole_0(X21,X22),X23)
      | r1_tarski(X21,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_62,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_63,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_59]),c_0_25])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0))) ),
    inference(rw,[status(thm)],[c_0_60,c_0_22])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0))) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_65])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k2_xboole_0(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( r1_xboole_0(X1,esk3_0)
    | ~ r1_xboole_0(X1,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_34])).

cnf(c_0_73,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_70,c_0_58])).

cnf(c_0_74,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_75,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_73,c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0)
    | ~ r1_xboole_0(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0)),X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_69])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77])])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_30]),c_0_79]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:09:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.56  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.20/0.56  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.56  #
% 0.20/0.56  # Preprocessing time       : 0.027 s
% 0.20/0.56  
% 0.20/0.56  # Proof found!
% 0.20/0.56  # SZS status Theorem
% 0.20/0.56  # SZS output start CNFRefutation
% 0.20/0.56  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.20/0.56  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.56  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.56  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.20/0.56  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.56  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.20/0.56  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.20/0.56  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.56  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.56  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.20/0.56  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.56  fof(t106_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.20/0.56  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.20/0.56  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.20/0.56  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.56  fof(c_0_15, plain, ![X27, X28]:r1_tarski(k4_xboole_0(X27,X28),X27), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.20/0.56  fof(c_0_16, plain, ![X19, X20]:k4_xboole_0(X19,X20)=k5_xboole_0(X19,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.56  fof(c_0_17, plain, ![X32, X33]:k4_xboole_0(X32,k4_xboole_0(X32,X33))=k3_xboole_0(X32,X33), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.56  fof(c_0_18, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.20/0.56  fof(c_0_19, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.56  fof(c_0_20, plain, ![X38, X39]:r1_xboole_0(k4_xboole_0(X38,X39),X39), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.20/0.56  cnf(c_0_21, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.56  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.56  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.56  cnf(c_0_24, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.56  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.56  cnf(c_0_26, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.56  fof(c_0_27, plain, ![X10]:k3_xboole_0(X10,X10)=X10, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.20/0.56  fof(c_0_28, plain, ![X31]:k4_xboole_0(X31,k1_xboole_0)=X31, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.56  fof(c_0_29, plain, ![X25, X26]:(~r1_tarski(X25,X26)|k3_xboole_0(X25,X26)=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.56  cnf(c_0_30, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.56  cnf(c_0_31, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_22]), c_0_22])).
% 0.20/0.56  cnf(c_0_32, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X2,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.56  cnf(c_0_33, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.56  cnf(c_0_34, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_26, c_0_22])).
% 0.20/0.56  cnf(c_0_35, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.56  cnf(c_0_36, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.56  fof(c_0_37, plain, ![X29, X30]:k2_xboole_0(X29,k4_xboole_0(X30,X29))=k2_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.20/0.56  cnf(c_0_38, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.56  cnf(c_0_39, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.56  cnf(c_0_40, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.56  cnf(c_0_41, plain, (r1_xboole_0(k5_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.56  cnf(c_0_42, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_36, c_0_22])).
% 0.20/0.56  cnf(c_0_43, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.56  cnf(c_0_44, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_25])).
% 0.20/0.56  cnf(c_0_45, plain, (r1_xboole_0(X1,k5_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.56  cnf(c_0_46, plain, (k5_xboole_0(X1,X1)=k3_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_42]), c_0_35])).
% 0.20/0.56  cnf(c_0_47, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_43, c_0_22])).
% 0.20/0.56  cnf(c_0_48, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_33, c_0_44])).
% 0.20/0.56  cnf(c_0_49, plain, (r1_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.56  fof(c_0_50, plain, ![X24]:k2_xboole_0(X24,k1_xboole_0)=X24, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.56  fof(c_0_51, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3)))), inference(assume_negation,[status(cth)],[t106_xboole_1])).
% 0.20/0.56  fof(c_0_52, plain, ![X35, X36, X37]:((r1_xboole_0(X35,k2_xboole_0(X36,X37))|~r1_xboole_0(X35,X36)|~r1_xboole_0(X35,X37))&((r1_xboole_0(X35,X36)|~r1_xboole_0(X35,k2_xboole_0(X36,X37)))&(r1_xboole_0(X35,X37)|~r1_xboole_0(X35,k2_xboole_0(X36,X37))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.20/0.56  cnf(c_0_53, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_25])).
% 0.20/0.56  cnf(c_0_54, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.56  cnf(c_0_55, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.56  fof(c_0_56, negated_conjecture, (r1_tarski(esk3_0,k4_xboole_0(esk4_0,esk5_0))&(~r1_tarski(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_51])])])).
% 0.20/0.56  cnf(c_0_57, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.56  cnf(c_0_58, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_44]), c_0_46]), c_0_54]), c_0_55])).
% 0.20/0.56  cnf(c_0_59, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_39, c_0_25])).
% 0.20/0.56  cnf(c_0_60, negated_conjecture, (r1_tarski(esk3_0,k4_xboole_0(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.56  fof(c_0_61, plain, ![X21, X22, X23]:(~r1_tarski(k2_xboole_0(X21,X22),X23)|r1_tarski(X21,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.20/0.56  fof(c_0_62, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.56  cnf(c_0_63, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.56  cnf(c_0_64, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_59]), c_0_25])).
% 0.20/0.56  cnf(c_0_65, negated_conjecture, (r1_tarski(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0)))), inference(rw,[status(thm)],[c_0_60, c_0_22])).
% 0.20/0.56  cnf(c_0_66, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.56  cnf(c_0_67, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.56  cnf(c_0_68, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.56  cnf(c_0_69, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0)))=esk3_0), inference(spm,[status(thm)],[c_0_38, c_0_65])).
% 0.20/0.56  cnf(c_0_70, plain, (r1_tarski(X1,X2)|~r1_tarski(k2_xboole_0(X3,X1),X2)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.56  cnf(c_0_71, negated_conjecture, (r1_xboole_0(X1,esk3_0)|~r1_xboole_0(X1,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.56  cnf(c_0_72, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_40, c_0_34])).
% 0.20/0.56  cnf(c_0_73, plain, (r1_tarski(k3_xboole_0(X1,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_70, c_0_58])).
% 0.20/0.56  cnf(c_0_74, negated_conjecture, (r1_xboole_0(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.56  cnf(c_0_75, plain, (r1_tarski(k3_xboole_0(X1,X2),X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_73, c_0_64])).
% 0.20/0.56  cnf(c_0_76, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.56  cnf(c_0_77, negated_conjecture, (r1_xboole_0(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_40, c_0_74])).
% 0.20/0.56  cnf(c_0_78, negated_conjecture, (r1_tarski(esk3_0,X1)|~r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0)),X1)), inference(spm,[status(thm)],[c_0_75, c_0_69])).
% 0.20/0.56  cnf(c_0_79, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77])])).
% 0.20/0.56  cnf(c_0_80, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_30]), c_0_79]), ['proof']).
% 0.20/0.56  # SZS output end CNFRefutation
% 0.20/0.56  # Proof object total steps             : 81
% 0.20/0.56  # Proof object clause steps            : 50
% 0.20/0.56  # Proof object formula steps           : 31
% 0.20/0.56  # Proof object conjectures             : 13
% 0.20/0.56  # Proof object clause conjectures      : 10
% 0.20/0.56  # Proof object formula conjectures     : 3
% 0.20/0.56  # Proof object initial clauses used    : 17
% 0.20/0.56  # Proof object initial formulas used   : 15
% 0.20/0.56  # Proof object generating inferences   : 25
% 0.20/0.56  # Proof object simplifying inferences  : 17
% 0.20/0.56  # Training examples: 0 positive, 0 negative
% 0.20/0.56  # Parsed axioms                        : 18
% 0.20/0.56  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.56  # Initial clauses                      : 23
% 0.20/0.56  # Removed in clause preprocessing      : 1
% 0.20/0.56  # Initial clauses in saturation        : 22
% 0.20/0.56  # Processed clauses                    : 4344
% 0.20/0.56  # ...of these trivial                  : 173
% 0.20/0.56  # ...subsumed                          : 3592
% 0.20/0.56  # ...remaining for further processing  : 579
% 0.20/0.56  # Other redundant clauses eliminated   : 0
% 0.20/0.56  # Clauses deleted for lack of memory   : 0
% 0.20/0.56  # Backward-subsumed                    : 26
% 0.20/0.56  # Backward-rewritten                   : 22
% 0.20/0.56  # Generated clauses                    : 28017
% 0.20/0.56  # ...of the previous two non-trivial   : 21383
% 0.20/0.56  # Contextual simplify-reflections      : 7
% 0.20/0.56  # Paramodulations                      : 28010
% 0.20/0.56  # Factorizations                       : 0
% 0.20/0.56  # Equation resolutions                 : 2
% 0.20/0.56  # Propositional unsat checks           : 0
% 0.20/0.56  #    Propositional check models        : 0
% 0.20/0.56  #    Propositional check unsatisfiable : 0
% 0.20/0.56  #    Propositional clauses             : 0
% 0.20/0.56  #    Propositional clauses after purity: 0
% 0.20/0.56  #    Propositional unsat core size     : 0
% 0.20/0.56  #    Propositional preprocessing time  : 0.000
% 0.20/0.56  #    Propositional encoding time       : 0.000
% 0.20/0.56  #    Propositional solver time         : 0.000
% 0.20/0.56  #    Success case prop preproc time    : 0.000
% 0.20/0.56  #    Success case prop encoding time   : 0.000
% 0.20/0.56  #    Success case prop solver time     : 0.000
% 0.20/0.56  # Current number of processed clauses  : 528
% 0.20/0.56  #    Positive orientable unit clauses  : 120
% 0.20/0.56  #    Positive unorientable unit clauses: 2
% 0.20/0.56  #    Negative unit clauses             : 23
% 0.20/0.56  #    Non-unit-clauses                  : 383
% 0.20/0.56  # Current number of unprocessed clauses: 16864
% 0.20/0.56  # ...number of literals in the above   : 40693
% 0.20/0.56  # Current number of archived formulas  : 0
% 0.20/0.56  # Current number of archived clauses   : 51
% 0.20/0.56  # Clause-clause subsumption calls (NU) : 62469
% 0.20/0.56  # Rec. Clause-clause subsumption calls : 60315
% 0.20/0.56  # Non-unit clause-clause subsumptions  : 3133
% 0.20/0.56  # Unit Clause-clause subsumption calls : 3281
% 0.20/0.56  # Rewrite failures with RHS unbound    : 0
% 0.20/0.56  # BW rewrite match attempts            : 1107
% 0.20/0.56  # BW rewrite match successes           : 21
% 0.20/0.56  # Condensation attempts                : 0
% 0.20/0.56  # Condensation successes               : 0
% 0.20/0.56  # Termbank termtop insertions          : 268061
% 0.20/0.56  
% 0.20/0.56  # -------------------------------------------------
% 0.20/0.56  # User time                : 0.217 s
% 0.20/0.56  # System time              : 0.013 s
% 0.20/0.56  # Total time               : 0.230 s
% 0.20/0.56  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
