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
% DateTime   : Thu Dec  3 10:44:50 EST 2020

% Result     : Theorem 0.79s
% Output     : CNFRefutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 200 expanded)
%              Number of clauses        :   54 (  87 expanded)
%              Number of leaves         :   16 (  52 expanded)
%              Depth                    :   17
%              Number of atoms          :  144 ( 400 expanded)
%              Number of equality atoms :   45 ( 111 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

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

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(t78_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X9,X10] :
      ( ( ~ r1_xboole_0(X9,X10)
        | k3_xboole_0(X9,X10) = k1_xboole_0 )
      & ( k3_xboole_0(X9,X10) != k1_xboole_0
        | r1_xboole_0(X9,X10) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_18,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))
    & r2_hidden(esk6_0,esk5_0)
    & r1_xboole_0(esk5_0,esk4_0)
    & ~ r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_19,plain,(
    ! [X19,X20,X22,X23,X24] :
      ( ( r1_xboole_0(X19,X20)
        | r2_hidden(esk2_2(X19,X20),k3_xboole_0(X19,X20)) )
      & ( ~ r2_hidden(X24,k3_xboole_0(X22,X23))
        | ~ r1_xboole_0(X22,X23) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_24,plain,(
    ! [X13,X14,X16,X17,X18] :
      ( ( r2_hidden(esk1_2(X13,X14),X13)
        | r1_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_2(X13,X14),X14)
        | r1_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X18,X16)
        | ~ r2_hidden(X18,X17)
        | ~ r1_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_25,plain,(
    ! [X11,X12] :
      ( ~ r1_xboole_0(X11,X12)
      | r1_xboole_0(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_21])])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_28,plain,(
    ! [X37] : k2_tarski(X37,X37) = k1_tarski(X37) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_29,plain,(
    ! [X38,X39] : k1_enumset1(X38,X38,X39) = k2_tarski(X38,X39) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_30,plain,(
    ! [X40,X41,X42] : k2_enumset1(X40,X40,X41,X42) = k1_enumset1(X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_31,plain,(
    ! [X27,X28,X29] : k3_xboole_0(k3_xboole_0(X27,X28),X29) = k3_xboole_0(X27,k3_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_38,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_39,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_41,plain,(
    ! [X30,X31] :
      ( ~ r1_tarski(X30,X31)
      | k3_xboole_0(X30,X31) = X30 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_44,plain,(
    ! [X43,X44] :
      ( r2_hidden(X43,X44)
      | r1_xboole_0(k1_tarski(X43),X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

cnf(c_0_45,negated_conjecture,
    ( k3_xboole_0(esk5_0,k3_xboole_0(esk4_0,X1)) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_23])).

cnf(c_0_46,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_40])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,esk3_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_53,negated_conjecture,
    ( k3_xboole_0(esk5_0,k3_xboole_0(esk4_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk4_0,esk3_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) = k3_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(esk6_0,X1)
    | ~ r1_xboole_0(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_58,negated_conjecture,
    ( r1_xboole_0(esk5_0,k3_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_59,plain,(
    ! [X32,X33,X34] :
      ( ~ r1_xboole_0(X32,X33)
      | k3_xboole_0(X32,k2_xboole_0(X33,X34)) = k3_xboole_0(X32,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).

fof(c_0_60,plain,(
    ! [X35,X36] : k2_xboole_0(X35,X36) = k5_xboole_0(X35,k4_xboole_0(X36,X35)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_61,plain,(
    ! [X25,X26] : k4_xboole_0(X25,X26) = k5_xboole_0(X25,k3_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4)))
    | ~ r1_xboole_0(X4,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_39])).

cnf(c_0_63,negated_conjecture,
    ( k3_xboole_0(esk4_0,k3_xboole_0(esk3_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))) = k3_xboole_0(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_55,c_0_39])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),X1)
    | ~ r1_xboole_0(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( r1_xboole_0(k3_xboole_0(esk4_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_58])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_hidden(X1,k3_xboole_0(esk4_0,esk3_0))
    | ~ r1_xboole_0(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),k3_xboole_0(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( r1_xboole_0(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),k3_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) = k3_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_21])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_hidden(X1,k3_xboole_0(esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])])).

cnf(c_0_74,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_75,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_76,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(X1,k3_xboole_0(X1,esk5_0)))) = k3_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_79,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(X1,k3_xboole_0(X1,esk5_0)))),k3_xboole_0(esk4_0,X1))
    | r1_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(X1,k3_xboole_0(X1,esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(esk3_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk3_0))),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_67]),c_0_68])).

cnf(c_0_83,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_67]),c_0_67]),c_0_68]),c_0_68])).

cnf(c_0_84,negated_conjecture,
    ( r1_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(esk3_0,k3_xboole_0(esk5_0,esk3_0)))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_43]),c_0_43]),c_0_26])).

cnf(c_0_85,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(esk5_0,k5_xboole_0(esk3_0,k3_xboole_0(esk5_0,esk3_0))),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83]),c_0_43])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_84]),c_0_85]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:07:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.79/0.94  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EI
% 0.79/0.94  # and selection function SelectLComplex.
% 0.79/0.94  #
% 0.79/0.94  # Preprocessing time       : 0.028 s
% 0.79/0.94  # Presaturation interreduction done
% 0.79/0.94  
% 0.79/0.94  # Proof found!
% 0.79/0.94  # SZS status Theorem
% 0.79/0.94  # SZS output start CNFRefutation
% 0.79/0.94  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 0.79/0.94  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.79/0.94  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.79/0.94  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.79/0.94  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.79/0.94  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.79/0.94  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.79/0.94  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.79/0.94  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.79/0.94  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.79/0.94  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.79/0.94  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.79/0.94  fof(t78_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 0.79/0.94  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.79/0.94  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.79/0.94  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.79/0.94  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 0.79/0.94  fof(c_0_17, plain, ![X9, X10]:((~r1_xboole_0(X9,X10)|k3_xboole_0(X9,X10)=k1_xboole_0)&(k3_xboole_0(X9,X10)!=k1_xboole_0|r1_xboole_0(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.79/0.94  fof(c_0_18, negated_conjecture, (((r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))&r2_hidden(esk6_0,esk5_0))&r1_xboole_0(esk5_0,esk4_0))&~r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.79/0.94  fof(c_0_19, plain, ![X19, X20, X22, X23, X24]:((r1_xboole_0(X19,X20)|r2_hidden(esk2_2(X19,X20),k3_xboole_0(X19,X20)))&(~r2_hidden(X24,k3_xboole_0(X22,X23))|~r1_xboole_0(X22,X23))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.79/0.94  cnf(c_0_20, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.79/0.94  cnf(c_0_21, negated_conjecture, (r1_xboole_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.79/0.94  cnf(c_0_22, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.79/0.94  cnf(c_0_23, negated_conjecture, (k3_xboole_0(esk5_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.79/0.94  fof(c_0_24, plain, ![X13, X14, X16, X17, X18]:(((r2_hidden(esk1_2(X13,X14),X13)|r1_xboole_0(X13,X14))&(r2_hidden(esk1_2(X13,X14),X14)|r1_xboole_0(X13,X14)))&(~r2_hidden(X18,X16)|~r2_hidden(X18,X17)|~r1_xboole_0(X16,X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.79/0.94  fof(c_0_25, plain, ![X11, X12]:(~r1_xboole_0(X11,X12)|r1_xboole_0(X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.79/0.94  cnf(c_0_26, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_21])])).
% 0.79/0.94  cnf(c_0_27, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.79/0.94  fof(c_0_28, plain, ![X37]:k2_tarski(X37,X37)=k1_tarski(X37), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.79/0.94  fof(c_0_29, plain, ![X38, X39]:k1_enumset1(X38,X38,X39)=k2_tarski(X38,X39), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.79/0.94  fof(c_0_30, plain, ![X40, X41, X42]:k2_enumset1(X40,X40,X41,X42)=k1_enumset1(X40,X41,X42), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.79/0.94  fof(c_0_31, plain, ![X27, X28, X29]:k3_xboole_0(k3_xboole_0(X27,X28),X29)=k3_xboole_0(X27,k3_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.79/0.94  cnf(c_0_32, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.79/0.94  cnf(c_0_33, negated_conjecture, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.79/0.94  cnf(c_0_34, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.79/0.94  cnf(c_0_35, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.79/0.94  cnf(c_0_36, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.79/0.94  cnf(c_0_37, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.79/0.94  fof(c_0_38, plain, ![X7, X8]:k3_xboole_0(X7,X8)=k3_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.79/0.94  cnf(c_0_39, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.79/0.94  cnf(c_0_40, negated_conjecture, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.79/0.94  fof(c_0_41, plain, ![X30, X31]:(~r1_tarski(X30,X31)|k3_xboole_0(X30,X31)=X30), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.79/0.94  cnf(c_0_42, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,esk4_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37])).
% 0.79/0.94  cnf(c_0_43, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.79/0.94  fof(c_0_44, plain, ![X43, X44]:(r2_hidden(X43,X44)|r1_xboole_0(k1_tarski(X43),X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.79/0.94  cnf(c_0_45, negated_conjecture, (k3_xboole_0(esk5_0,k3_xboole_0(esk4_0,X1))=k3_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_23])).
% 0.79/0.94  cnf(c_0_46, negated_conjecture, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_40])).
% 0.79/0.94  cnf(c_0_47, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.79/0.94  cnf(c_0_48, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,esk3_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.79/0.94  cnf(c_0_49, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.79/0.94  cnf(c_0_50, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.79/0.94  cnf(c_0_51, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.79/0.94  cnf(c_0_52, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.79/0.94  cnf(c_0_53, negated_conjecture, (k3_xboole_0(esk5_0,k3_xboole_0(esk4_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.79/0.94  cnf(c_0_54, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_22, c_0_43])).
% 0.79/0.94  cnf(c_0_55, negated_conjecture, (k3_xboole_0(k3_xboole_0(esk4_0,esk3_0),k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))=k3_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.79/0.94  cnf(c_0_56, negated_conjecture, (~r2_hidden(esk6_0,X1)|~r1_xboole_0(X1,esk5_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.79/0.94  cnf(c_0_57, plain, (r2_hidden(X1,X2)|r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_35]), c_0_36]), c_0_37])).
% 0.79/0.94  cnf(c_0_58, negated_conjecture, (r1_xboole_0(esk5_0,k3_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.79/0.94  fof(c_0_59, plain, ![X32, X33, X34]:(~r1_xboole_0(X32,X33)|k3_xboole_0(X32,k2_xboole_0(X33,X34))=k3_xboole_0(X32,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).
% 0.79/0.94  fof(c_0_60, plain, ![X35, X36]:k2_xboole_0(X35,X36)=k5_xboole_0(X35,k4_xboole_0(X36,X35)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.79/0.94  fof(c_0_61, plain, ![X25, X26]:k4_xboole_0(X25,X26)=k5_xboole_0(X25,k3_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.79/0.94  cnf(c_0_62, plain, (~r2_hidden(X1,k3_xboole_0(X2,k3_xboole_0(X3,X4)))|~r1_xboole_0(X4,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_54, c_0_39])).
% 0.79/0.94  cnf(c_0_63, negated_conjecture, (k3_xboole_0(esk4_0,k3_xboole_0(esk3_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)))=k3_xboole_0(esk4_0,esk3_0)), inference(rw,[status(thm)],[c_0_55, c_0_39])).
% 0.79/0.94  cnf(c_0_64, negated_conjecture, (r1_xboole_0(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),X1)|~r1_xboole_0(X1,esk5_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.79/0.94  cnf(c_0_65, negated_conjecture, (r1_xboole_0(k3_xboole_0(esk4_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_58])).
% 0.79/0.94  cnf(c_0_66, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.79/0.94  cnf(c_0_67, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.79/0.94  cnf(c_0_68, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.79/0.94  cnf(c_0_69, negated_conjecture, (~r2_hidden(X1,k3_xboole_0(esk4_0,esk3_0))|~r1_xboole_0(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),k3_xboole_0(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.79/0.94  cnf(c_0_70, negated_conjecture, (r1_xboole_0(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),k3_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.79/0.94  cnf(c_0_71, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))=k3_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67]), c_0_68])).
% 0.79/0.94  cnf(c_0_72, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_21])).
% 0.79/0.94  cnf(c_0_73, negated_conjecture, (~r2_hidden(X1,k3_xboole_0(esk4_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70])])).
% 0.79/0.94  cnf(c_0_74, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.79/0.94  fof(c_0_75, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.79/0.94  cnf(c_0_76, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(X1,k3_xboole_0(X1,esk5_0))))=k3_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.79/0.94  cnf(c_0_77, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.79/0.94  cnf(c_0_78, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.79/0.94  cnf(c_0_79, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.79/0.94  cnf(c_0_80, negated_conjecture, (r2_hidden(esk2_2(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(X1,k3_xboole_0(X1,esk5_0)))),k3_xboole_0(esk4_0,X1))|r1_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(X1,k3_xboole_0(X1,esk5_0))))), inference(spm,[status(thm)],[c_0_74, c_0_76])).
% 0.79/0.94  cnf(c_0_81, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_77])).
% 0.79/0.94  cnf(c_0_82, negated_conjecture, (~r1_xboole_0(k5_xboole_0(esk3_0,k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,esk3_0))),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_67]), c_0_68])).
% 0.79/0.94  cnf(c_0_83, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_67]), c_0_67]), c_0_68]), c_0_68])).
% 0.79/0.94  cnf(c_0_84, negated_conjecture, (r1_xboole_0(esk4_0,k5_xboole_0(esk5_0,k5_xboole_0(esk3_0,k3_xboole_0(esk5_0,esk3_0))))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_43]), c_0_43]), c_0_26])).
% 0.79/0.94  cnf(c_0_85, negated_conjecture, (~r1_xboole_0(k5_xboole_0(esk5_0,k5_xboole_0(esk3_0,k3_xboole_0(esk5_0,esk3_0))),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83]), c_0_43])).
% 0.79/0.94  cnf(c_0_86, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_84]), c_0_85]), ['proof']).
% 0.79/0.94  # SZS output end CNFRefutation
% 0.79/0.94  # Proof object total steps             : 87
% 0.79/0.94  # Proof object clause steps            : 54
% 0.79/0.94  # Proof object formula steps           : 33
% 0.79/0.94  # Proof object conjectures             : 34
% 0.79/0.94  # Proof object clause conjectures      : 31
% 0.79/0.94  # Proof object formula conjectures     : 3
% 0.79/0.94  # Proof object initial clauses used    : 22
% 0.79/0.94  # Proof object initial formulas used   : 16
% 0.79/0.94  # Proof object generating inferences   : 22
% 0.79/0.94  # Proof object simplifying inferences  : 27
% 0.79/0.94  # Training examples: 0 positive, 0 negative
% 0.79/0.94  # Parsed axioms                        : 16
% 0.79/0.94  # Removed by relevancy pruning/SinE    : 0
% 0.79/0.94  # Initial clauses                      : 23
% 0.79/0.94  # Removed in clause preprocessing      : 5
% 0.79/0.94  # Initial clauses in saturation        : 18
% 0.79/0.94  # Processed clauses                    : 7591
% 0.79/0.94  # ...of these trivial                  : 1395
% 0.79/0.94  # ...subsumed                          : 5355
% 0.79/0.94  # ...remaining for further processing  : 841
% 0.79/0.94  # Other redundant clauses eliminated   : 0
% 0.79/0.94  # Clauses deleted for lack of memory   : 0
% 0.79/0.94  # Backward-subsumed                    : 4
% 0.79/0.94  # Backward-rewritten                   : 48
% 0.79/0.94  # Generated clauses                    : 69407
% 0.79/0.94  # ...of the previous two non-trivial   : 49520
% 0.79/0.94  # Contextual simplify-reflections      : 0
% 0.79/0.94  # Paramodulations                      : 69407
% 0.79/0.94  # Factorizations                       : 0
% 0.79/0.94  # Equation resolutions                 : 0
% 0.79/0.94  # Propositional unsat checks           : 0
% 0.79/0.94  #    Propositional check models        : 0
% 0.79/0.94  #    Propositional check unsatisfiable : 0
% 0.79/0.94  #    Propositional clauses             : 0
% 0.79/0.94  #    Propositional clauses after purity: 0
% 0.79/0.94  #    Propositional unsat core size     : 0
% 0.79/0.94  #    Propositional preprocessing time  : 0.000
% 0.79/0.94  #    Propositional encoding time       : 0.000
% 0.79/0.94  #    Propositional solver time         : 0.000
% 0.79/0.94  #    Success case prop preproc time    : 0.000
% 0.79/0.94  #    Success case prop encoding time   : 0.000
% 0.79/0.94  #    Success case prop solver time     : 0.000
% 0.79/0.94  # Current number of processed clauses  : 771
% 0.79/0.94  #    Positive orientable unit clauses  : 315
% 0.79/0.94  #    Positive unorientable unit clauses: 40
% 0.79/0.94  #    Negative unit clauses             : 5
% 0.79/0.94  #    Non-unit-clauses                  : 411
% 0.79/0.94  # Current number of unprocessed clauses: 41904
% 0.79/0.94  # ...number of literals in the above   : 67356
% 0.79/0.94  # Current number of archived formulas  : 0
% 0.79/0.94  # Current number of archived clauses   : 75
% 0.79/0.94  # Clause-clause subsumption calls (NU) : 52226
% 0.79/0.94  # Rec. Clause-clause subsumption calls : 51011
% 0.79/0.94  # Non-unit clause-clause subsumptions  : 1387
% 0.79/0.94  # Unit Clause-clause subsumption calls : 822
% 0.79/0.94  # Rewrite failures with RHS unbound    : 0
% 0.79/0.94  # BW rewrite match attempts            : 998
% 0.79/0.94  # BW rewrite match successes           : 214
% 0.79/0.94  # Condensation attempts                : 0
% 0.79/0.94  # Condensation successes               : 0
% 0.79/0.94  # Termbank termtop insertions          : 1279547
% 0.79/0.94  
% 0.79/0.94  # -------------------------------------------------
% 0.79/0.94  # User time                : 0.579 s
% 0.79/0.94  # System time              : 0.017 s
% 0.79/0.94  # Total time               : 0.596 s
% 0.79/0.94  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
