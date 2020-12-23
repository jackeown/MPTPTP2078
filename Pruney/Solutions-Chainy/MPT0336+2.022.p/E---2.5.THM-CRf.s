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
% DateTime   : Thu Dec  3 10:44:51 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 351 expanded)
%              Number of clauses        :   67 ( 159 expanded)
%              Number of leaves         :   15 (  91 expanded)
%              Depth                    :   18
%              Number of atoms          :  170 ( 686 expanded)
%              Number of equality atoms :   40 ( 162 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

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

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t81_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
     => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(c_0_15,plain,(
    ! [X9,X10] :
      ( ~ r1_xboole_0(X9,X10)
      | r1_xboole_0(X10,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_16,plain,(
    ! [X23] : r1_xboole_0(X23,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_17,plain,(
    ! [X35,X36] :
      ( ( k4_xboole_0(X35,k1_tarski(X36)) != X35
        | ~ r2_hidden(X36,X35) )
      & ( r2_hidden(X36,X35)
        | k4_xboole_0(X35,k1_tarski(X36)) = X35 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_18,plain,(
    ! [X32] : k2_tarski(X32,X32) = k1_tarski(X32) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_19,plain,(
    ! [X33,X34] : k2_enumset1(X33,X33,X33,X34) = k2_tarski(X33,X34) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_20,plain,(
    ! [X30,X31] :
      ( ( ~ r1_xboole_0(X30,X31)
        | k4_xboole_0(X30,X31) = X30 )
      & ( k4_xboole_0(X30,X31) != X30
        | r1_xboole_0(X30,X31) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_21,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_24,plain,(
    ! [X18,X19] : k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k3_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

fof(c_0_26,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_2(X11,X12),X12)
        | r1_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_34,plain,(
    ! [X17] : k4_xboole_0(X17,k1_xboole_0) = X17 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_35,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))
    & r2_hidden(esk5_0,esk4_0)
    & r1_xboole_0(esk4_0,esk3_0)
    & ~ r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

fof(c_0_38,plain,(
    ! [X27,X28,X29] :
      ( ~ r1_xboole_0(X27,k4_xboole_0(X28,X29))
      | r1_xboole_0(X28,k4_xboole_0(X27,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_33])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)) = X1
    | ~ r2_hidden(X2,X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X2,k4_xboole_0(X1,X3))
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(esk5_0,X1)
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( k4_xboole_0(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = X1
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_43])).

cnf(c_0_50,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_22])])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_47])).

fof(c_0_52,plain,(
    ! [X24,X25,X26] :
      ( ( r1_xboole_0(X24,k2_xboole_0(X25,X26))
        | ~ r1_xboole_0(X24,X25)
        | ~ r1_xboole_0(X24,X26) )
      & ( r1_xboole_0(X24,X25)
        | ~ r1_xboole_0(X24,k2_xboole_0(X25,X26)) )
      & ( r1_xboole_0(X24,X26)
        | ~ r1_xboole_0(X24,k2_xboole_0(X25,X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = X1
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_37])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk4_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = k4_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(esk3_0,k4_xboole_0(X1,esk4_0))
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_51])).

cnf(c_0_57,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_50])).

cnf(c_0_58,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_59,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(X20,X21)
      | ~ r1_xboole_0(X21,X22)
      | r1_xboole_0(X20,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_28]),c_0_29]),c_0_33])).

cnf(c_0_61,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_62,negated_conjecture,
    ( k4_xboole_0(esk3_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_47])).

cnf(c_0_63,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,esk4_0),k4_xboole_0(X2,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))
    | ~ r1_xboole_0(X2,k4_xboole_0(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(X1,esk3_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_65,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_66,negated_conjecture,
    ( r1_xboole_0(esk4_0,k2_xboole_0(X1,esk3_0))
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_42])).

cnf(c_0_67,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_60,c_0_40])).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_70,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_22])).

cnf(c_0_71,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,esk3_0),esk4_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_62])).

cnf(c_0_72,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( r1_xboole_0(esk4_0,k2_xboole_0(k1_xboole_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_22])).

cnf(c_0_74,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)),X1)
    | ~ r1_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,esk3_0),esk4_0),k2_xboole_0(k1_xboole_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(k1_xboole_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(k1_xboole_0,esk3_0),k4_xboole_0(k4_xboole_0(X1,esk3_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,esk3_0),esk4_0) = k2_xboole_0(k1_xboole_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)),k2_xboole_0(k1_xboole_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_78]),c_0_72])).

cnf(c_0_82,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(X1,esk3_0),k2_xboole_0(k1_xboole_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_79]),c_0_80])).

cnf(c_0_83,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3)))
    | ~ r1_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_40])).

cnf(c_0_84,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(k1_xboole_0,esk3_0),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(k1_xboole_0,esk3_0),k4_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( r1_xboole_0(esk2_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,esk3_0),k4_xboole_0(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,esk3_0),k4_xboole_0(X1,esk3_0)) = k2_xboole_0(k1_xboole_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_xboole_0(X1,esk4_0))
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_47])).

cnf(c_0_89,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_90,negated_conjecture,
    ( r1_xboole_0(esk2_0,k2_xboole_0(k1_xboole_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,k4_xboole_0(X1,esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_50]),c_0_72])).

cnf(c_0_92,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_94,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(esk4_0,k4_xboole_0(X1,esk3_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_92])).

cnf(c_0_96,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk4_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_93,c_0_72])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:14:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.52  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EI
% 0.19/0.52  # and selection function SelectLComplex.
% 0.19/0.52  #
% 0.19/0.52  # Preprocessing time       : 0.027 s
% 0.19/0.52  # Presaturation interreduction done
% 0.19/0.52  
% 0.19/0.52  # Proof found!
% 0.19/0.52  # SZS status Theorem
% 0.19/0.52  # SZS output start CNFRefutation
% 0.19/0.52  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.52  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.52  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.19/0.52  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.52  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 0.19/0.52  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.19/0.52  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.52  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.52  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 0.19/0.52  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.52  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.52  fof(t81_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 0.19/0.52  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.19/0.52  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.19/0.52  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.52  fof(c_0_15, plain, ![X9, X10]:(~r1_xboole_0(X9,X10)|r1_xboole_0(X10,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.52  fof(c_0_16, plain, ![X23]:r1_xboole_0(X23,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.52  fof(c_0_17, plain, ![X35, X36]:((k4_xboole_0(X35,k1_tarski(X36))!=X35|~r2_hidden(X36,X35))&(r2_hidden(X36,X35)|k4_xboole_0(X35,k1_tarski(X36))=X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.19/0.52  fof(c_0_18, plain, ![X32]:k2_tarski(X32,X32)=k1_tarski(X32), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.52  fof(c_0_19, plain, ![X33, X34]:k2_enumset1(X33,X33,X33,X34)=k2_tarski(X33,X34), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.19/0.52  fof(c_0_20, plain, ![X30, X31]:((~r1_xboole_0(X30,X31)|k4_xboole_0(X30,X31)=X30)&(k4_xboole_0(X30,X31)!=X30|r1_xboole_0(X30,X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.19/0.52  cnf(c_0_21, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.52  cnf(c_0_22, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.52  fof(c_0_23, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.52  fof(c_0_24, plain, ![X18, X19]:k4_xboole_0(X18,k4_xboole_0(X18,X19))=k3_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.52  fof(c_0_25, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 0.19/0.52  fof(c_0_26, plain, ![X11, X12, X14, X15, X16]:(((r2_hidden(esk1_2(X11,X12),X11)|r1_xboole_0(X11,X12))&(r2_hidden(esk1_2(X11,X12),X12)|r1_xboole_0(X11,X12)))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|~r1_xboole_0(X14,X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.52  cnf(c_0_27, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.52  cnf(c_0_28, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.52  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.52  cnf(c_0_30, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.52  cnf(c_0_31, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.52  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.52  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.52  fof(c_0_34, plain, ![X17]:k4_xboole_0(X17,k1_xboole_0)=X17, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.52  fof(c_0_35, negated_conjecture, (((r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))&r2_hidden(esk5_0,esk4_0))&r1_xboole_0(esk4_0,esk3_0))&~r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.19/0.52  cnf(c_0_36, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.52  cnf(c_0_37, plain, (k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.19/0.52  fof(c_0_38, plain, ![X27, X28, X29]:(~r1_xboole_0(X27,k4_xboole_0(X28,X29))|r1_xboole_0(X28,k4_xboole_0(X27,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).
% 0.19/0.52  cnf(c_0_39, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.52  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_33])).
% 0.19/0.52  cnf(c_0_41, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.52  cnf(c_0_42, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.52  cnf(c_0_43, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.52  cnf(c_0_44, plain, (k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))=X1|~r2_hidden(X2,X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.52  cnf(c_0_45, plain, (r1_xboole_0(X2,k4_xboole_0(X1,X3))|~r1_xboole_0(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.52  cnf(c_0_46, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.19/0.52  cnf(c_0_47, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_42])).
% 0.19/0.52  cnf(c_0_48, negated_conjecture, (~r2_hidden(esk5_0,X1)|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_43])).
% 0.19/0.52  cnf(c_0_49, negated_conjecture, (k4_xboole_0(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=X1|~r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_44, c_0_43])).
% 0.19/0.52  cnf(c_0_50, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_22])])).
% 0.19/0.52  cnf(c_0_51, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=esk3_0), inference(spm,[status(thm)],[c_0_30, c_0_47])).
% 0.19/0.52  fof(c_0_52, plain, ![X24, X25, X26]:((r1_xboole_0(X24,k2_xboole_0(X25,X26))|~r1_xboole_0(X24,X25)|~r1_xboole_0(X24,X26))&((r1_xboole_0(X24,X25)|~r1_xboole_0(X24,k2_xboole_0(X25,X26)))&(r1_xboole_0(X24,X26)|~r1_xboole_0(X24,k2_xboole_0(X25,X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.19/0.52  cnf(c_0_53, negated_conjecture, (r1_tarski(k3_xboole_0(esk2_0,esk3_0),k1_tarski(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.52  cnf(c_0_54, negated_conjecture, (k4_xboole_0(X1,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=X1|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_48, c_0_37])).
% 0.19/0.52  cnf(c_0_55, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk4_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=k4_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.52  cnf(c_0_56, negated_conjecture, (r1_xboole_0(esk3_0,k4_xboole_0(X1,esk4_0))|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_45, c_0_51])).
% 0.19/0.52  cnf(c_0_57, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_21, c_0_50])).
% 0.19/0.52  cnf(c_0_58, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.52  fof(c_0_59, plain, ![X20, X21, X22]:(~r1_tarski(X20,X21)|~r1_xboole_0(X21,X22)|r1_xboole_0(X20,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.19/0.52  cnf(c_0_60, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_28]), c_0_29]), c_0_33])).
% 0.19/0.52  cnf(c_0_61, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.52  cnf(c_0_62, negated_conjecture, (k4_xboole_0(esk3_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))=esk3_0), inference(spm,[status(thm)],[c_0_54, c_0_47])).
% 0.19/0.52  cnf(c_0_63, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,esk4_0),k4_xboole_0(X2,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))|~r1_xboole_0(X2,k4_xboole_0(X1,esk4_0))), inference(spm,[status(thm)],[c_0_45, c_0_55])).
% 0.19/0.52  cnf(c_0_64, negated_conjecture, (r1_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(X1,esk3_0),esk4_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.52  fof(c_0_65, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.52  cnf(c_0_66, negated_conjecture, (r1_xboole_0(esk4_0,k2_xboole_0(X1,esk3_0))|~r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_58, c_0_42])).
% 0.19/0.52  cnf(c_0_67, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.52  cnf(c_0_68, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[c_0_60, c_0_40])).
% 0.19/0.52  cnf(c_0_69, negated_conjecture, (r1_xboole_0(esk3_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.52  cnf(c_0_70, plain, (r1_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_58, c_0_22])).
% 0.19/0.52  cnf(c_0_71, negated_conjecture, (r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,esk3_0),esk4_0),esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_62])).
% 0.19/0.52  cnf(c_0_72, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.52  cnf(c_0_73, negated_conjecture, (r1_xboole_0(esk4_0,k2_xboole_0(k1_xboole_0,esk3_0))), inference(spm,[status(thm)],[c_0_66, c_0_22])).
% 0.19/0.52  cnf(c_0_74, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)),X1)|~r1_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.52  cnf(c_0_75, negated_conjecture, (r1_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_69])).
% 0.19/0.52  cnf(c_0_76, negated_conjecture, (r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,esk3_0),esk4_0),k2_xboole_0(k1_xboole_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])).
% 0.19/0.52  cnf(c_0_77, negated_conjecture, (r1_xboole_0(k2_xboole_0(k1_xboole_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_73])).
% 0.19/0.52  cnf(c_0_78, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)),esk3_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.19/0.52  cnf(c_0_79, negated_conjecture, (r1_xboole_0(k2_xboole_0(k1_xboole_0,esk3_0),k4_xboole_0(k4_xboole_0(X1,esk3_0),esk4_0))), inference(spm,[status(thm)],[c_0_21, c_0_76])).
% 0.19/0.52  cnf(c_0_80, negated_conjecture, (k4_xboole_0(k2_xboole_0(k1_xboole_0,esk3_0),esk4_0)=k2_xboole_0(k1_xboole_0,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_77])).
% 0.19/0.52  cnf(c_0_81, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)),k2_xboole_0(k1_xboole_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_78]), c_0_72])).
% 0.19/0.52  cnf(c_0_82, negated_conjecture, (r1_xboole_0(k4_xboole_0(X1,esk3_0),k2_xboole_0(k1_xboole_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_79]), c_0_80])).
% 0.19/0.52  cnf(c_0_83, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3)))|~r1_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_45, c_0_40])).
% 0.19/0.52  cnf(c_0_84, negated_conjecture, (r1_xboole_0(k2_xboole_0(k1_xboole_0,esk3_0),k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk2_0)))), inference(spm,[status(thm)],[c_0_21, c_0_81])).
% 0.19/0.52  cnf(c_0_85, negated_conjecture, (r1_xboole_0(k2_xboole_0(k1_xboole_0,esk3_0),k4_xboole_0(X1,esk3_0))), inference(spm,[status(thm)],[c_0_21, c_0_82])).
% 0.19/0.52  cnf(c_0_86, negated_conjecture, (r1_xboole_0(esk2_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,esk3_0),k4_xboole_0(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.19/0.52  cnf(c_0_87, negated_conjecture, (k4_xboole_0(k2_xboole_0(k1_xboole_0,esk3_0),k4_xboole_0(X1,esk3_0))=k2_xboole_0(k1_xboole_0,esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_85])).
% 0.19/0.52  cnf(c_0_88, negated_conjecture, (r1_xboole_0(esk3_0,k2_xboole_0(X1,esk4_0))|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_58, c_0_47])).
% 0.19/0.52  cnf(c_0_89, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.52  cnf(c_0_90, negated_conjecture, (r1_xboole_0(esk2_0,k2_xboole_0(k1_xboole_0,esk3_0))), inference(rw,[status(thm)],[c_0_86, c_0_87])).
% 0.19/0.52  cnf(c_0_91, negated_conjecture, (r1_xboole_0(esk3_0,k2_xboole_0(esk4_0,k4_xboole_0(X1,esk3_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_50]), c_0_72])).
% 0.19/0.52  cnf(c_0_92, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.19/0.52  cnf(c_0_93, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk2_0,esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.52  cnf(c_0_94, negated_conjecture, (r1_xboole_0(k2_xboole_0(esk4_0,k4_xboole_0(X1,esk3_0)),esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_91])).
% 0.19/0.52  cnf(c_0_95, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=esk2_0), inference(spm,[status(thm)],[c_0_30, c_0_92])).
% 0.19/0.52  cnf(c_0_96, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk4_0,esk2_0),esk3_0)), inference(rw,[status(thm)],[c_0_93, c_0_72])).
% 0.19/0.52  cnf(c_0_97, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96]), ['proof']).
% 0.19/0.52  # SZS output end CNFRefutation
% 0.19/0.52  # Proof object total steps             : 98
% 0.19/0.52  # Proof object clause steps            : 67
% 0.19/0.52  # Proof object formula steps           : 31
% 0.19/0.52  # Proof object conjectures             : 44
% 0.19/0.52  # Proof object clause conjectures      : 41
% 0.19/0.52  # Proof object formula conjectures     : 3
% 0.19/0.52  # Proof object initial clauses used    : 20
% 0.19/0.52  # Proof object initial formulas used   : 15
% 0.19/0.52  # Proof object generating inferences   : 41
% 0.19/0.52  # Proof object simplifying inferences  : 19
% 0.19/0.52  # Training examples: 0 positive, 0 negative
% 0.19/0.52  # Parsed axioms                        : 15
% 0.19/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.52  # Initial clauses                      : 24
% 0.19/0.52  # Removed in clause preprocessing      : 3
% 0.19/0.52  # Initial clauses in saturation        : 21
% 0.19/0.52  # Processed clauses                    : 750
% 0.19/0.52  # ...of these trivial                  : 72
% 0.19/0.52  # ...subsumed                          : 55
% 0.19/0.52  # ...remaining for further processing  : 623
% 0.19/0.52  # Other redundant clauses eliminated   : 5
% 0.19/0.52  # Clauses deleted for lack of memory   : 0
% 0.19/0.52  # Backward-subsumed                    : 2
% 0.19/0.52  # Backward-rewritten                   : 84
% 0.19/0.52  # Generated clauses                    : 13495
% 0.19/0.52  # ...of the previous two non-trivial   : 11899
% 0.19/0.52  # Contextual simplify-reflections      : 0
% 0.19/0.52  # Paramodulations                      : 13490
% 0.19/0.52  # Factorizations                       : 0
% 0.19/0.52  # Equation resolutions                 : 5
% 0.19/0.52  # Propositional unsat checks           : 0
% 0.19/0.52  #    Propositional check models        : 0
% 0.19/0.52  #    Propositional check unsatisfiable : 0
% 0.19/0.52  #    Propositional clauses             : 0
% 0.19/0.52  #    Propositional clauses after purity: 0
% 0.19/0.52  #    Propositional unsat core size     : 0
% 0.19/0.52  #    Propositional preprocessing time  : 0.000
% 0.19/0.52  #    Propositional encoding time       : 0.000
% 0.19/0.52  #    Propositional solver time         : 0.000
% 0.19/0.52  #    Success case prop preproc time    : 0.000
% 0.19/0.52  #    Success case prop encoding time   : 0.000
% 0.19/0.52  #    Success case prop solver time     : 0.000
% 0.19/0.52  # Current number of processed clauses  : 516
% 0.19/0.52  #    Positive orientable unit clauses  : 359
% 0.19/0.52  #    Positive unorientable unit clauses: 2
% 0.19/0.52  #    Negative unit clauses             : 10
% 0.19/0.52  #    Non-unit-clauses                  : 145
% 0.19/0.52  # Current number of unprocessed clauses: 11094
% 0.19/0.52  # ...number of literals in the above   : 12897
% 0.19/0.52  # Current number of archived formulas  : 0
% 0.19/0.52  # Current number of archived clauses   : 110
% 0.19/0.52  # Clause-clause subsumption calls (NU) : 3270
% 0.19/0.52  # Rec. Clause-clause subsumption calls : 3186
% 0.19/0.52  # Non-unit clause-clause subsumptions  : 41
% 0.19/0.52  # Unit Clause-clause subsumption calls : 4056
% 0.19/0.52  # Rewrite failures with RHS unbound    : 0
% 0.19/0.52  # BW rewrite match attempts            : 834
% 0.19/0.52  # BW rewrite match successes           : 22
% 0.19/0.52  # Condensation attempts                : 0
% 0.19/0.52  # Condensation successes               : 0
% 0.19/0.52  # Termbank termtop insertions          : 297324
% 0.19/0.52  
% 0.19/0.52  # -------------------------------------------------
% 0.19/0.52  # User time                : 0.168 s
% 0.19/0.52  # System time              : 0.012 s
% 0.19/0.52  # Total time               : 0.180 s
% 0.19/0.52  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
