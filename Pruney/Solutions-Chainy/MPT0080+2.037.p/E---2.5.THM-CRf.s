%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:12 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 331 expanded)
%              Number of clauses        :   52 ( 152 expanded)
%              Number of leaves         :   14 (  88 expanded)
%              Depth                    :   17
%              Number of atoms          :  133 ( 507 expanded)
%              Number of equality atoms :   44 ( 265 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t73_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(c_0_14,plain,(
    ! [X16,X17,X19,X20,X21] :
      ( ( r1_xboole_0(X16,X17)
        | r2_hidden(esk2_2(X16,X17),k3_xboole_0(X16,X17)) )
      & ( ~ r2_hidden(X21,k3_xboole_0(X19,X20))
        | ~ r1_xboole_0(X19,X20) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_15,plain,(
    ! [X32,X33] : k4_xboole_0(X32,k4_xboole_0(X32,X33)) = k3_xboole_0(X32,X33) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_16,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k3_xboole_0(X6,X7) = k1_xboole_0 )
      & ( k3_xboole_0(X6,X7) != k1_xboole_0
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X24] : k4_xboole_0(X24,k1_xboole_0) = X24 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X1,k1_xboole_0)
    | k4_xboole_0(X1,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

fof(c_0_26,plain,(
    ! [X25,X26] : k4_xboole_0(k2_xboole_0(X25,X26),X26) = k4_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_28,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_22])).

fof(c_0_29,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_2(X10,X11),X11)
        | r1_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_30,plain,(
    ! [X22,X23] : k2_xboole_0(X22,k4_xboole_0(X23,X22)) = k2_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_31,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_32,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28])])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X3) )
       => r1_tarski(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t73_xboole_1])).

fof(c_0_37,plain,(
    ! [X27,X28,X29] : k4_xboole_0(k4_xboole_0(X27,X28),X29) = k4_xboole_0(X27,k2_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_32]),c_0_22])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_18])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_43,plain,(
    ! [X30,X31] : k4_xboole_0(X30,k3_xboole_0(X30,X31)) = k4_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_44,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk4_0,esk5_0))
    & r1_xboole_0(esk3_0,esk5_0)
    & ~ r1_tarski(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).

cnf(c_0_45,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_32]),c_0_38])).

cnf(c_0_47,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_22]),c_0_42])])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_50,plain,(
    ! [X34,X35,X36] :
      ( ~ r1_tarski(X34,X35)
      | ~ r1_xboole_0(X35,X36)
      | r1_xboole_0(X34,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_52,plain,(
    ! [X8,X9] :
      ( ~ r1_xboole_0(X8,X9)
      | r1_xboole_0(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_53,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X3)
    | k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3)))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_45]),c_0_45])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_40])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_48]),c_0_38])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_49,c_0_18])).

cnf(c_0_57,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(esk5_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_39])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_38]),c_0_55])])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( r1_xboole_0(esk3_0,X1)
    | ~ r1_xboole_0(k2_xboole_0(esk5_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_35])).

cnf(c_0_65,negated_conjecture,
    ( r1_xboole_0(esk3_0,k4_xboole_0(X1,k2_xboole_0(esk5_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

fof(c_0_66,plain,(
    ! [X37,X38] : r1_tarski(X37,k2_xboole_0(X37,X38)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_48]),c_0_22])).

cnf(c_0_68,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_70,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_45])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_39])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_39])).

cnf(c_0_74,negated_conjecture,
    ( k2_xboole_0(esk4_0,k4_xboole_0(esk3_0,esk5_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_40])).

cnf(c_0_75,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_48]),c_0_40]),c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_41]),c_0_40]),c_0_39]),c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])]),c_0_79]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:47:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_C48_F1_AE_CS_SP_PS_S0Y
% 0.13/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.027 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.13/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.40  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.13/0.40  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.13/0.40  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.13/0.40  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.13/0.40  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.13/0.40  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.13/0.40  fof(t73_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 0.13/0.40  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.13/0.40  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.13/0.40  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.13/0.40  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.13/0.40  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.13/0.40  fof(c_0_14, plain, ![X16, X17, X19, X20, X21]:((r1_xboole_0(X16,X17)|r2_hidden(esk2_2(X16,X17),k3_xboole_0(X16,X17)))&(~r2_hidden(X21,k3_xboole_0(X19,X20))|~r1_xboole_0(X19,X20))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.13/0.40  fof(c_0_15, plain, ![X32, X33]:k4_xboole_0(X32,k4_xboole_0(X32,X33))=k3_xboole_0(X32,X33), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.40  fof(c_0_16, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k3_xboole_0(X6,X7)=k1_xboole_0)&(k3_xboole_0(X6,X7)!=k1_xboole_0|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.13/0.40  cnf(c_0_17, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_18, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  fof(c_0_19, plain, ![X24]:k4_xboole_0(X24,k1_xboole_0)=X24, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.13/0.40  cnf(c_0_20, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_21, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.40  cnf(c_0_22, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  cnf(c_0_23, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_20, c_0_18])).
% 0.13/0.40  cnf(c_0_24, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.40  cnf(c_0_25, plain, (r1_xboole_0(X1,k1_xboole_0)|k4_xboole_0(X1,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_22])).
% 0.13/0.40  fof(c_0_26, plain, ![X25, X26]:k4_xboole_0(k2_xboole_0(X25,X26),X26)=k4_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.13/0.40  cnf(c_0_27, plain, (~r2_hidden(X1,k1_xboole_0)|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_22])).
% 0.13/0.40  cnf(c_0_28, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_22])).
% 0.13/0.40  fof(c_0_29, plain, ![X10, X11, X13, X14, X15]:(((r2_hidden(esk1_2(X10,X11),X10)|r1_xboole_0(X10,X11))&(r2_hidden(esk1_2(X10,X11),X11)|r1_xboole_0(X10,X11)))&(~r2_hidden(X15,X13)|~r2_hidden(X15,X14)|~r1_xboole_0(X13,X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.13/0.40  fof(c_0_30, plain, ![X22, X23]:k2_xboole_0(X22,k4_xboole_0(X23,X22))=k2_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.13/0.40  fof(c_0_31, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.13/0.40  cnf(c_0_32, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.40  cnf(c_0_33, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_34, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28])])).
% 0.13/0.40  cnf(c_0_35, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.40  fof(c_0_36, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2))), inference(assume_negation,[status(cth)],[t73_xboole_1])).
% 0.13/0.40  fof(c_0_37, plain, ![X27, X28, X29]:k4_xboole_0(k4_xboole_0(X27,X28),X29)=k4_xboole_0(X27,k2_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.13/0.40  cnf(c_0_38, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.40  cnf(c_0_39, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.40  cnf(c_0_40, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_32]), c_0_22])).
% 0.13/0.40  cnf(c_0_41, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_18])).
% 0.13/0.40  cnf(c_0_42, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.40  fof(c_0_43, plain, ![X30, X31]:k4_xboole_0(X30,k3_xboole_0(X30,X31))=k4_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.13/0.40  fof(c_0_44, negated_conjecture, ((r1_tarski(esk3_0,k2_xboole_0(esk4_0,esk5_0))&r1_xboole_0(esk3_0,esk5_0))&~r1_tarski(esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).
% 0.13/0.40  cnf(c_0_45, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.40  cnf(c_0_46, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_32]), c_0_38])).
% 0.13/0.40  cnf(c_0_47, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.40  cnf(c_0_48, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_22]), c_0_42])])).
% 0.13/0.40  cnf(c_0_49, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.40  fof(c_0_50, plain, ![X34, X35, X36]:(~r1_tarski(X34,X35)|~r1_xboole_0(X35,X36)|r1_xboole_0(X34,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.13/0.40  cnf(c_0_51, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.40  fof(c_0_52, plain, ![X8, X9]:(~r1_xboole_0(X8,X9)|r1_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.13/0.40  cnf(c_0_53, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X3)|k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3))))!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_45]), c_0_45])).
% 0.13/0.40  cnf(c_0_54, plain, (k2_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_40])).
% 0.13/0.40  cnf(c_0_55, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_48]), c_0_38])).
% 0.13/0.40  cnf(c_0_56, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_49, c_0_18])).
% 0.13/0.40  cnf(c_0_57, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.40  cnf(c_0_58, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(esk5_0,esk4_0))), inference(rw,[status(thm)],[c_0_51, c_0_39])).
% 0.13/0.40  cnf(c_0_59, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.40  cnf(c_0_60, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_38]), c_0_55])])).
% 0.13/0.40  cnf(c_0_61, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X2,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_21, c_0_56])).
% 0.13/0.40  cnf(c_0_62, negated_conjecture, (r1_xboole_0(esk3_0,X1)|~r1_xboole_0(k2_xboole_0(esk5_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.13/0.40  cnf(c_0_63, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.13/0.40  cnf(c_0_64, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X2,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_61, c_0_35])).
% 0.13/0.40  cnf(c_0_65, negated_conjecture, (r1_xboole_0(esk3_0,k4_xboole_0(X1,k2_xboole_0(esk5_0,esk4_0)))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.13/0.40  fof(c_0_66, plain, ![X37, X38]:r1_tarski(X37,k2_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.13/0.40  cnf(c_0_67, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_48]), c_0_22])).
% 0.13/0.40  cnf(c_0_68, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0)))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.13/0.40  cnf(c_0_69, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.13/0.40  cnf(c_0_70, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_38, c_0_45])).
% 0.13/0.40  cnf(c_0_71, negated_conjecture, (k4_xboole_0(esk3_0,k2_xboole_0(esk5_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.13/0.40  cnf(c_0_72, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_32, c_0_39])).
% 0.13/0.40  cnf(c_0_73, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_69, c_0_39])).
% 0.13/0.40  cnf(c_0_74, negated_conjecture, (k2_xboole_0(esk4_0,k4_xboole_0(esk3_0,esk5_0))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_40])).
% 0.13/0.40  cnf(c_0_75, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_48]), c_0_40]), c_0_72])).
% 0.13/0.40  cnf(c_0_76, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.13/0.40  cnf(c_0_77, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_41]), c_0_40]), c_0_39]), c_0_75])).
% 0.13/0.40  cnf(c_0_78, negated_conjecture, (r1_xboole_0(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.40  cnf(c_0_79, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.40  cnf(c_0_80, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])]), c_0_79]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 81
% 0.13/0.40  # Proof object clause steps            : 52
% 0.13/0.40  # Proof object formula steps           : 29
% 0.13/0.40  # Proof object conjectures             : 14
% 0.13/0.40  # Proof object clause conjectures      : 11
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 17
% 0.13/0.40  # Proof object initial formulas used   : 14
% 0.13/0.40  # Proof object generating inferences   : 29
% 0.13/0.40  # Proof object simplifying inferences  : 27
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 14
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 20
% 0.13/0.40  # Removed in clause preprocessing      : 1
% 0.13/0.40  # Initial clauses in saturation        : 19
% 0.13/0.40  # Processed clauses                    : 556
% 0.13/0.40  # ...of these trivial                  : 17
% 0.13/0.40  # ...subsumed                          : 377
% 0.13/0.40  # ...remaining for further processing  : 162
% 0.13/0.40  # Other redundant clauses eliminated   : 0
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 5
% 0.13/0.40  # Backward-rewritten                   : 14
% 0.13/0.40  # Generated clauses                    : 2038
% 0.13/0.40  # ...of the previous two non-trivial   : 1423
% 0.13/0.40  # Contextual simplify-reflections      : 1
% 0.13/0.40  # Paramodulations                      : 2038
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 0
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 124
% 0.13/0.40  #    Positive orientable unit clauses  : 46
% 0.13/0.40  #    Positive unorientable unit clauses: 1
% 0.13/0.40  #    Negative unit clauses             : 9
% 0.13/0.40  #    Non-unit-clauses                  : 68
% 0.13/0.40  # Current number of unprocessed clauses: 880
% 0.13/0.40  # ...number of literals in the above   : 1631
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 39
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 1781
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 1391
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 235
% 0.13/0.40  # Unit Clause-clause subsumption calls : 345
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 74
% 0.13/0.40  # BW rewrite match successes           : 21
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 16797
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.051 s
% 0.13/0.40  # System time              : 0.006 s
% 0.13/0.40  # Total time               : 0.056 s
% 0.13/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
