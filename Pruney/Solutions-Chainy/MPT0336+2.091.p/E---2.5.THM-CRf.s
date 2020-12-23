%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:00 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 539 expanded)
%              Number of clauses        :   54 ( 234 expanded)
%              Number of leaves         :   15 ( 149 expanded)
%              Depth                    :   16
%              Number of atoms          :  161 ( 727 expanded)
%              Number of equality atoms :   44 ( 443 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t88_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

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

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

fof(c_0_16,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))
    & r2_hidden(esk6_0,esk5_0)
    & r1_xboole_0(esk5_0,esk4_0)
    & ~ r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_17,plain,(
    ! [X44] : k2_tarski(X44,X44) = k1_tarski(X44) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X25,X26] : k4_xboole_0(X25,k4_xboole_0(X25,X26)) = k3_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_19,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_20,plain,(
    ! [X22,X23] :
      ( ~ r1_tarski(X22,X23)
      | k3_xboole_0(X22,X23) = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X27,X28,X29] : k3_xboole_0(X27,k4_xboole_0(X28,X29)) = k4_xboole_0(k3_xboole_0(X27,X28),X29) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k2_tarski(esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_23]),c_0_23])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)),k2_tarski(esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_23]),c_0_23])).

fof(c_0_33,plain,(
    ! [X30] : k4_xboole_0(k1_xboole_0,X30) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_34,plain,(
    ! [X42,X43] :
      ( ~ r1_xboole_0(X42,X43)
      | k4_xboole_0(k2_xboole_0(X42,X43),X43) = X42 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).

fof(c_0_35,plain,(
    ! [X21] : k2_xboole_0(X21,k1_xboole_0) = X21 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_36,plain,(
    ! [X34] : r1_xboole_0(X34,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_37,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k2_tarski(esk6_0,esk6_0))))))) = k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_32])).

cnf(c_0_38,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_42,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( r1_xboole_0(X15,X16)
        | r2_hidden(esk2_2(X15,X16),k3_xboole_0(X15,X16)) )
      & ( ~ r2_hidden(X20,k3_xboole_0(X18,X19))
        | ~ r1_xboole_0(X18,X19) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k2_tarski(esk6_0,esk6_0))))),X1))) = k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_37]),c_0_32])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))),X4))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X4))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_32]),c_0_32]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_28])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

fof(c_0_47,plain,(
    ! [X45,X46] :
      ( ( k4_xboole_0(X45,k1_tarski(X46)) != X45
        | ~ r2_hidden(X46,X45) )
      & ( r2_hidden(X46,X45)
        | k4_xboole_0(X45,k1_tarski(X46)) = X45 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k4_xboole_0(k2_tarski(esk6_0,esk6_0),X1))))))) = k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,X1))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_48,c_0_23])).

cnf(c_0_53,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k2_tarski(esk6_0,esk6_0)))) = k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_46])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,k2_tarski(X2,X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_51,c_0_22])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X4)))))))
    | ~ r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_32]),c_0_32])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))))))) = k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_53])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_54,c_0_23])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X2,k2_tarski(X1,X1)) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_55,c_0_22])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_46]),c_0_41])])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k2_tarski(X3,X3)))) != k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ r2_hidden(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_32])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))
    | ~ r1_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)),k2_tarski(esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_53]),c_0_58])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(X2,k2_tarski(X1,X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])).

fof(c_0_65,plain,(
    ! [X7,X8] :
      ( ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_66,plain,(
    ! [X35,X36,X37] :
      ( ( r1_xboole_0(X35,k2_xboole_0(X36,X37))
        | ~ r1_xboole_0(X35,X36)
        | ~ r1_xboole_0(X35,X37) )
      & ( r1_xboole_0(X35,X36)
        | ~ r1_xboole_0(X35,k2_xboole_0(X36,X37)) )
      & ( r1_xboole_0(X35,X37)
        | ~ r1_xboole_0(X35,k2_xboole_0(X36,X37)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

fof(c_0_67,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_xboole_0(X9,X10) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | r1_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk6_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))
    | ~ r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_28])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk6_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))
    | r1_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_59])).

cnf(c_0_77,plain,
    ( r1_xboole_0(k2_xboole_0(X1,X2),X3)
    | ~ r1_xboole_0(X3,X2)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_hidden(esk6_0,X1)
    | ~ r1_xboole_0(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk6_0,esk4_0)
    | r1_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_82,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(X1,esk5_0),esk4_0)
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_78])])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.48  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.48  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.48  #
% 0.20/0.48  # Preprocessing time       : 0.028 s
% 0.20/0.48  # Presaturation interreduction done
% 0.20/0.48  
% 0.20/0.48  # Proof found!
% 0.20/0.48  # SZS status Theorem
% 0.20/0.48  # SZS output start CNFRefutation
% 0.20/0.48  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 0.20/0.48  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.48  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.48  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.48  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.48  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.20/0.48  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.20/0.48  fof(t88_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 0.20/0.48  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.48  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.20/0.48  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.48  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.20/0.48  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.48  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.20/0.48  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.48  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 0.20/0.48  fof(c_0_16, negated_conjecture, (((r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))&r2_hidden(esk6_0,esk5_0))&r1_xboole_0(esk5_0,esk4_0))&~r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.20/0.48  fof(c_0_17, plain, ![X44]:k2_tarski(X44,X44)=k1_tarski(X44), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.48  fof(c_0_18, plain, ![X25, X26]:k4_xboole_0(X25,k4_xboole_0(X25,X26))=k3_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.48  fof(c_0_19, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.48  fof(c_0_20, plain, ![X22, X23]:(~r1_tarski(X22,X23)|k3_xboole_0(X22,X23)=X22), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.48  cnf(c_0_21, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_22, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.48  cnf(c_0_23, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.48  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.48  fof(c_0_25, plain, ![X27, X28, X29]:k3_xboole_0(X27,k4_xboole_0(X28,X29))=k4_xboole_0(k3_xboole_0(X27,X28),X29), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.20/0.48  cnf(c_0_26, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.48  cnf(c_0_27, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k2_tarski(esk6_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.20/0.48  cnf(c_0_28, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_23]), c_0_23])).
% 0.20/0.48  cnf(c_0_29, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.48  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_23])).
% 0.20/0.48  cnf(c_0_31, negated_conjecture, (r1_tarski(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)),k2_tarski(esk6_0,esk6_0))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.48  cnf(c_0_32, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_23]), c_0_23])).
% 0.20/0.48  fof(c_0_33, plain, ![X30]:k4_xboole_0(k1_xboole_0,X30)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.20/0.48  fof(c_0_34, plain, ![X42, X43]:(~r1_xboole_0(X42,X43)|k4_xboole_0(k2_xboole_0(X42,X43),X43)=X42), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_xboole_1])])).
% 0.20/0.48  fof(c_0_35, plain, ![X21]:k2_xboole_0(X21,k1_xboole_0)=X21, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.48  fof(c_0_36, plain, ![X34]:r1_xboole_0(X34,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.20/0.48  cnf(c_0_37, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k2_tarski(esk6_0,esk6_0)))))))=k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_32])).
% 0.20/0.48  cnf(c_0_38, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.48  cnf(c_0_39, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.48  cnf(c_0_40, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.48  cnf(c_0_41, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.48  fof(c_0_42, plain, ![X15, X16, X18, X19, X20]:((r1_xboole_0(X15,X16)|r2_hidden(esk2_2(X15,X16),k3_xboole_0(X15,X16)))&(~r2_hidden(X20,k3_xboole_0(X18,X19))|~r1_xboole_0(X18,X19))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.48  cnf(c_0_43, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k2_tarski(esk6_0,esk6_0))))),X1)))=k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_37]), c_0_32])).
% 0.20/0.48  cnf(c_0_44, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))),X4)))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X4)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_32]), c_0_32]), c_0_32]), c_0_32]), c_0_32])).
% 0.20/0.48  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_28])).
% 0.20/0.48  cnf(c_0_46, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])])).
% 0.20/0.48  fof(c_0_47, plain, ![X45, X46]:((k4_xboole_0(X45,k1_tarski(X46))!=X45|~r2_hidden(X46,X45))&(r2_hidden(X46,X45)|k4_xboole_0(X45,k1_tarski(X46))=X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.20/0.48  cnf(c_0_48, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.48  cnf(c_0_49, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k4_xboole_0(k2_tarski(esk6_0,esk6_0),X1)))))))=k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,X1)))), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.48  cnf(c_0_50, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.48  cnf(c_0_51, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.48  cnf(c_0_52, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_48, c_0_23])).
% 0.20/0.48  cnf(c_0_53, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k2_tarski(esk6_0,esk6_0))))=k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_46])).
% 0.20/0.48  cnf(c_0_54, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.48  cnf(c_0_55, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.48  cnf(c_0_56, plain, (k4_xboole_0(X1,k2_tarski(X2,X2))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_51, c_0_22])).
% 0.20/0.48  cnf(c_0_57, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X4)))))))|~r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_32]), c_0_32])).
% 0.20/0.48  cnf(c_0_58, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))))))))=k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))), inference(rw,[status(thm)],[c_0_37, c_0_53])).
% 0.20/0.48  cnf(c_0_59, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_54, c_0_23])).
% 0.20/0.48  cnf(c_0_60, plain, (k4_xboole_0(X2,k2_tarski(X1,X1))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_55, c_0_22])).
% 0.20/0.48  cnf(c_0_61, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_46]), c_0_41])])).
% 0.20/0.48  cnf(c_0_62, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k2_tarski(X3,X3))))!=k4_xboole_0(X1,k4_xboole_0(X1,X2))|~r2_hidden(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_56, c_0_32])).
% 0.20/0.48  cnf(c_0_63, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))|~r1_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)),k2_tarski(esk6_0,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_53]), c_0_58])).
% 0.20/0.48  cnf(c_0_64, plain, (r2_hidden(X1,X2)|r1_xboole_0(X2,k2_tarski(X1,X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])).
% 0.20/0.48  fof(c_0_65, plain, ![X7, X8]:(~r1_xboole_0(X7,X8)|r1_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.48  fof(c_0_66, plain, ![X35, X36, X37]:((r1_xboole_0(X35,k2_xboole_0(X36,X37))|~r1_xboole_0(X35,X36)|~r1_xboole_0(X35,X37))&((r1_xboole_0(X35,X36)|~r1_xboole_0(X35,k2_xboole_0(X36,X37)))&(r1_xboole_0(X35,X37)|~r1_xboole_0(X35,k2_xboole_0(X36,X37))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.20/0.48  fof(c_0_67, plain, ![X9, X10, X12, X13, X14]:(((r2_hidden(esk1_2(X9,X10),X9)|r1_xboole_0(X9,X10))&(r2_hidden(esk1_2(X9,X10),X10)|r1_xboole_0(X9,X10)))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|~r1_xboole_0(X12,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.48  cnf(c_0_68, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_62, c_0_60])).
% 0.20/0.48  cnf(c_0_69, negated_conjecture, (r2_hidden(esk6_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))|~r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.48  cnf(c_0_70, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.48  cnf(c_0_71, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.48  cnf(c_0_72, negated_conjecture, (r1_xboole_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_73, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.48  cnf(c_0_74, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_75, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_68, c_0_28])).
% 0.20/0.48  cnf(c_0_76, negated_conjecture, (r2_hidden(esk6_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))|r1_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_69, c_0_59])).
% 0.20/0.48  cnf(c_0_77, plain, (r1_xboole_0(k2_xboole_0(X1,X2),X3)|~r1_xboole_0(X3,X2)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.20/0.48  cnf(c_0_78, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_70, c_0_72])).
% 0.20/0.48  cnf(c_0_79, negated_conjecture, (~r2_hidden(esk6_0,X1)|~r1_xboole_0(X1,esk5_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.20/0.48  cnf(c_0_80, negated_conjecture, (r2_hidden(esk6_0,esk4_0)|r1_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.48  cnf(c_0_81, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.48  cnf(c_0_82, negated_conjecture, (r1_xboole_0(k2_xboole_0(X1,esk5_0),esk4_0)|~r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.20/0.48  cnf(c_0_83, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_78])])).
% 0.20/0.48  cnf(c_0_84, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83])]), ['proof']).
% 0.20/0.48  # SZS output end CNFRefutation
% 0.20/0.48  # Proof object total steps             : 85
% 0.20/0.48  # Proof object clause steps            : 54
% 0.20/0.48  # Proof object formula steps           : 31
% 0.20/0.48  # Proof object conjectures             : 23
% 0.20/0.48  # Proof object clause conjectures      : 20
% 0.20/0.48  # Proof object formula conjectures     : 3
% 0.20/0.48  # Proof object initial clauses used    : 20
% 0.20/0.48  # Proof object initial formulas used   : 15
% 0.20/0.48  # Proof object generating inferences   : 22
% 0.20/0.48  # Proof object simplifying inferences  : 34
% 0.20/0.48  # Training examples: 0 positive, 0 negative
% 0.20/0.48  # Parsed axioms                        : 18
% 0.20/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.48  # Initial clauses                      : 27
% 0.20/0.48  # Removed in clause preprocessing      : 2
% 0.20/0.48  # Initial clauses in saturation        : 25
% 0.20/0.48  # Processed clauses                    : 1162
% 0.20/0.48  # ...of these trivial                  : 40
% 0.20/0.48  # ...subsumed                          : 722
% 0.20/0.48  # ...remaining for further processing  : 400
% 0.20/0.48  # Other redundant clauses eliminated   : 5
% 0.20/0.48  # Clauses deleted for lack of memory   : 0
% 0.20/0.48  # Backward-subsumed                    : 38
% 0.20/0.48  # Backward-rewritten                   : 107
% 0.20/0.48  # Generated clauses                    : 5219
% 0.20/0.48  # ...of the previous two non-trivial   : 4601
% 0.20/0.48  # Contextual simplify-reflections      : 0
% 0.20/0.48  # Paramodulations                      : 5214
% 0.20/0.48  # Factorizations                       : 0
% 0.20/0.48  # Equation resolutions                 : 5
% 0.20/0.48  # Propositional unsat checks           : 0
% 0.20/0.48  #    Propositional check models        : 0
% 0.20/0.48  #    Propositional check unsatisfiable : 0
% 0.20/0.48  #    Propositional clauses             : 0
% 0.20/0.48  #    Propositional clauses after purity: 0
% 0.20/0.48  #    Propositional unsat core size     : 0
% 0.20/0.48  #    Propositional preprocessing time  : 0.000
% 0.20/0.48  #    Propositional encoding time       : 0.000
% 0.20/0.48  #    Propositional solver time         : 0.000
% 0.20/0.48  #    Success case prop preproc time    : 0.000
% 0.20/0.48  #    Success case prop encoding time   : 0.000
% 0.20/0.48  #    Success case prop solver time     : 0.000
% 0.20/0.48  # Current number of processed clauses  : 230
% 0.20/0.48  #    Positive orientable unit clauses  : 42
% 0.20/0.48  #    Positive unorientable unit clauses: 5
% 0.20/0.48  #    Negative unit clauses             : 13
% 0.20/0.48  #    Non-unit-clauses                  : 170
% 0.20/0.48  # Current number of unprocessed clauses: 3419
% 0.20/0.48  # ...number of literals in the above   : 6785
% 0.20/0.48  # Current number of archived formulas  : 0
% 0.20/0.48  # Current number of archived clauses   : 172
% 0.20/0.48  # Clause-clause subsumption calls (NU) : 8338
% 0.20/0.48  # Rec. Clause-clause subsumption calls : 7664
% 0.20/0.48  # Non-unit clause-clause subsumptions  : 441
% 0.20/0.48  # Unit Clause-clause subsumption calls : 377
% 0.20/0.48  # Rewrite failures with RHS unbound    : 42
% 0.20/0.48  # BW rewrite match attempts            : 945
% 0.20/0.48  # BW rewrite match successes           : 127
% 0.20/0.48  # Condensation attempts                : 0
% 0.20/0.48  # Condensation successes               : 0
% 0.20/0.48  # Termbank termtop insertions          : 99754
% 0.20/0.48  
% 0.20/0.48  # -------------------------------------------------
% 0.20/0.48  # User time                : 0.126 s
% 0.20/0.48  # System time              : 0.010 s
% 0.20/0.48  # Total time               : 0.136 s
% 0.20/0.48  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
