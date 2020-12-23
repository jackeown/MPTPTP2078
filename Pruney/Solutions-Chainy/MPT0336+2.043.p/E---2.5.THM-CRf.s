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
% DateTime   : Thu Dec  3 10:44:54 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 229 expanded)
%              Number of clauses        :   54 ( 104 expanded)
%              Number of leaves         :   13 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  181 ( 579 expanded)
%              Number of equality atoms :   36 ( 112 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

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

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X41,X42] :
      ( r2_hidden(X41,X42)
      | r1_xboole_0(k1_tarski(X41),X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

fof(c_0_15,plain,(
    ! [X35] : k2_tarski(X35,X35) = k1_tarski(X35) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X36,X37] : k1_enumset1(X36,X36,X37) = k2_tarski(X36,X37) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X38,X39,X40] : k2_enumset1(X38,X38,X39,X40) = k1_enumset1(X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_18,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,esk5_0),k1_tarski(esk7_0))
    & r2_hidden(esk7_0,esk6_0)
    & r1_xboole_0(esk6_0,esk5_0)
    & ~ r1_xboole_0(k2_xboole_0(esk4_0,esk6_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_19,plain,(
    ! [X43,X44] : k3_tarski(k2_tarski(X43,X44)) = k2_xboole_0(X43,X44) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X24,X25,X27,X28,X29] :
      ( ( r1_xboole_0(X24,X25)
        | r2_hidden(esk3_2(X24,X25),k3_xboole_0(X24,X25)) )
      & ( ~ r2_hidden(X29,k3_xboole_0(X27,X28))
        | ~ r1_xboole_0(X27,X28) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,esk5_0),k1_tarski(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_27,plain,(
    ! [X32,X33,X34] :
      ( ( r1_xboole_0(X32,k2_xboole_0(X33,X34))
        | ~ r1_xboole_0(X32,X33)
        | ~ r1_xboole_0(X32,X34) )
      & ( r1_xboole_0(X32,X33)
        | ~ r1_xboole_0(X32,k2_xboole_0(X33,X34)) )
      & ( r1_xboole_0(X32,X34)
        | ~ r1_xboole_0(X32,k2_xboole_0(X33,X34)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_28,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X16,X17] :
      ( ~ r1_xboole_0(X16,X17)
      | r1_xboole_0(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])).

fof(c_0_32,plain,(
    ! [X30,X31] :
      ( ~ r1_tarski(X30,X31)
      | k3_xboole_0(X30,X31) = X30 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk4_0,esk5_0),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_23])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk5_0,esk4_0),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_42,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k3_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k3_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,k3_tarski(k2_enumset1(X2,X2,X2,X3)))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_24])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_45,plain,(
    ! [X18,X19,X21,X22,X23] :
      ( ( r2_hidden(esk2_2(X18,X19),X18)
        | r1_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_2(X18,X19),X19)
        | r1_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X23,X21)
        | ~ r2_hidden(X23,X22)
        | ~ r1_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk4_0,esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X3,k3_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk5_0,esk4_0),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)) = k3_xboole_0(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(esk5_0,k3_tarski(k2_enumset1(X1,X1,X1,esk6_0)))
    | ~ r1_xboole_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0)),esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_36]),c_0_24])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk7_0,k3_xboole_0(esk5_0,esk4_0))
    | ~ r2_hidden(X1,k3_xboole_0(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( r1_xboole_0(esk5_0,k3_tarski(k2_enumset1(X1,X1,X1,esk6_0)))
    | r2_hidden(esk2_2(esk5_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2))
    | ~ r2_hidden(X3,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk3_2(k3_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0)),esk5_0),k3_xboole_0(esk5_0,k3_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_52]),c_0_34])).

cnf(c_0_60,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(X1,k3_xboole_0(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_38])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( k3_xboole_0(X1,k3_xboole_0(esk5_0,esk4_0)) = k3_xboole_0(esk5_0,esk4_0)
    | r2_hidden(esk7_0,k3_xboole_0(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,X1),esk5_0)
    | ~ r2_hidden(X2,k3_xboole_0(esk5_0,k3_tarski(k2_enumset1(X1,X1,X1,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,k3_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0))),k3_xboole_0(esk5_0,k3_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( r1_xboole_0(esk5_0,k3_tarski(k2_enumset1(X1,X1,X1,esk6_0)))
    | r2_hidden(esk2_2(esk5_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( k3_xboole_0(X1,k3_xboole_0(esk6_0,esk5_0)) = k3_xboole_0(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_56])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_38])).

cnf(c_0_70,negated_conjecture,
    ( k3_xboole_0(X1,k3_xboole_0(esk5_0,esk4_0)) = k3_xboole_0(esk5_0,esk4_0)
    | r2_hidden(esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_72,plain,
    ( r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_52])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,X1),X1)
    | ~ r2_hidden(X2,k3_xboole_0(esk5_0,k3_tarski(k2_enumset1(X1,X1,X1,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk6_0,esk5_0),X1) = k3_xboole_0(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( k3_xboole_0(X1,k3_xboole_0(esk5_0,esk4_0)) = k3_xboole_0(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk3_2(X1,esk5_0),k3_xboole_0(X1,esk5_0))
    | ~ r2_hidden(esk2_2(esk5_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_66])).

cnf(c_0_79,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk4_0) = k3_xboole_0(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_34]),c_0_79]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.82/2.03  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 1.82/2.03  # and selection function SelectCQArNTNpEqFirst.
% 1.82/2.03  #
% 1.82/2.03  # Preprocessing time       : 0.028 s
% 1.82/2.03  # Presaturation interreduction done
% 1.82/2.03  
% 1.82/2.03  # Proof found!
% 1.82/2.03  # SZS status Theorem
% 1.82/2.03  # SZS output start CNFRefutation
% 1.82/2.03  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 1.82/2.03  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.82/2.03  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.82/2.03  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.82/2.03  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.82/2.03  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.82/2.03  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.82/2.03  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.82/2.03  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 1.82/2.03  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.82/2.03  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.82/2.03  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.82/2.03  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.82/2.03  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 1.82/2.03  fof(c_0_14, plain, ![X41, X42]:(r2_hidden(X41,X42)|r1_xboole_0(k1_tarski(X41),X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 1.82/2.03  fof(c_0_15, plain, ![X35]:k2_tarski(X35,X35)=k1_tarski(X35), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.82/2.03  fof(c_0_16, plain, ![X36, X37]:k1_enumset1(X36,X36,X37)=k2_tarski(X36,X37), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.82/2.03  fof(c_0_17, plain, ![X38, X39, X40]:k2_enumset1(X38,X38,X39,X40)=k1_enumset1(X38,X39,X40), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.82/2.03  fof(c_0_18, negated_conjecture, (((r1_tarski(k3_xboole_0(esk4_0,esk5_0),k1_tarski(esk7_0))&r2_hidden(esk7_0,esk6_0))&r1_xboole_0(esk6_0,esk5_0))&~r1_xboole_0(k2_xboole_0(esk4_0,esk6_0),esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 1.82/2.03  fof(c_0_19, plain, ![X43, X44]:k3_tarski(k2_tarski(X43,X44))=k2_xboole_0(X43,X44), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 1.82/2.03  fof(c_0_20, plain, ![X24, X25, X27, X28, X29]:((r1_xboole_0(X24,X25)|r2_hidden(esk3_2(X24,X25),k3_xboole_0(X24,X25)))&(~r2_hidden(X29,k3_xboole_0(X27,X28))|~r1_xboole_0(X27,X28))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 1.82/2.03  cnf(c_0_21, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.82/2.03  cnf(c_0_22, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.82/2.03  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.82/2.03  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.82/2.03  cnf(c_0_25, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,esk5_0),k1_tarski(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.82/2.03  fof(c_0_26, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.82/2.03  fof(c_0_27, plain, ![X32, X33, X34]:((r1_xboole_0(X32,k2_xboole_0(X33,X34))|~r1_xboole_0(X32,X33)|~r1_xboole_0(X32,X34))&((r1_xboole_0(X32,X33)|~r1_xboole_0(X32,k2_xboole_0(X33,X34)))&(r1_xboole_0(X32,X34)|~r1_xboole_0(X32,k2_xboole_0(X33,X34))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 1.82/2.03  cnf(c_0_28, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.82/2.03  fof(c_0_29, plain, ![X16, X17]:(~r1_xboole_0(X16,X17)|r1_xboole_0(X17,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 1.82/2.03  cnf(c_0_30, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.82/2.03  cnf(c_0_31, plain, (r2_hidden(X1,X2)|r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24])).
% 1.82/2.03  fof(c_0_32, plain, ![X30, X31]:(~r1_tarski(X30,X31)|k3_xboole_0(X30,X31)=X30), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 1.82/2.03  cnf(c_0_33, negated_conjecture, (r1_tarski(k3_xboole_0(esk4_0,esk5_0),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_22]), c_0_23]), c_0_24])).
% 1.82/2.03  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.82/2.03  cnf(c_0_35, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.82/2.03  cnf(c_0_36, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_23])).
% 1.82/2.03  cnf(c_0_37, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.82/2.03  cnf(c_0_38, negated_conjecture, (r1_xboole_0(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.82/2.03  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 1.82/2.03  cnf(c_0_40, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.82/2.03  cnf(c_0_41, negated_conjecture, (r1_tarski(k3_xboole_0(esk5_0,esk4_0),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 1.82/2.03  fof(c_0_42, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8))&(r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k3_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k3_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k3_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))&(r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k3_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 1.82/2.03  cnf(c_0_43, plain, (r1_xboole_0(X1,k3_tarski(k2_enumset1(X2,X2,X2,X3)))|~r1_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_24])).
% 1.82/2.03  cnf(c_0_44, negated_conjecture, (r1_xboole_0(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.82/2.03  fof(c_0_45, plain, ![X18, X19, X21, X22, X23]:(((r2_hidden(esk2_2(X18,X19),X18)|r1_xboole_0(X18,X19))&(r2_hidden(esk2_2(X18,X19),X19)|r1_xboole_0(X18,X19)))&(~r2_hidden(X23,X21)|~r2_hidden(X23,X22)|~r1_xboole_0(X21,X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 1.82/2.03  cnf(c_0_46, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk4_0,esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.82/2.03  cnf(c_0_47, plain, (r2_hidden(X1,X2)|~r2_hidden(X3,k3_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))), inference(spm,[status(thm)],[c_0_39, c_0_34])).
% 1.82/2.03  cnf(c_0_48, negated_conjecture, (k3_xboole_0(k3_xboole_0(esk5_0,esk4_0),k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))=k3_xboole_0(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 1.82/2.03  cnf(c_0_49, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.82/2.03  cnf(c_0_50, negated_conjecture, (r1_xboole_0(esk5_0,k3_tarski(k2_enumset1(X1,X1,X1,esk6_0)))|~r1_xboole_0(esk5_0,X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 1.82/2.03  cnf(c_0_51, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.82/2.03  cnf(c_0_52, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.82/2.03  cnf(c_0_53, negated_conjecture, (~r1_xboole_0(k3_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0)),esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_36]), c_0_24])).
% 1.82/2.03  cnf(c_0_54, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.82/2.03  cnf(c_0_55, negated_conjecture, (r2_hidden(esk7_0,k3_xboole_0(esk5_0,esk4_0))|~r2_hidden(X1,k3_xboole_0(esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 1.82/2.03  cnf(c_0_56, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_49])).
% 1.82/2.03  cnf(c_0_57, negated_conjecture, (r1_xboole_0(esk5_0,k3_tarski(k2_enumset1(X1,X1,X1,esk6_0)))|r2_hidden(esk2_2(esk5_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 1.82/2.03  cnf(c_0_58, plain, (r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2))|~r2_hidden(X3,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_30, c_0_52])).
% 1.82/2.03  cnf(c_0_59, negated_conjecture, (r2_hidden(esk3_2(k3_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0)),esk5_0),k3_xboole_0(esk5_0,k3_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_52]), c_0_34])).
% 1.82/2.03  cnf(c_0_60, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.82/2.03  cnf(c_0_61, negated_conjecture, (~r2_hidden(X1,k3_xboole_0(esk6_0,esk5_0))), inference(spm,[status(thm)],[c_0_30, c_0_38])).
% 1.82/2.03  cnf(c_0_62, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.82/2.03  cnf(c_0_63, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_54])).
% 1.82/2.03  cnf(c_0_64, negated_conjecture, (k3_xboole_0(X1,k3_xboole_0(esk5_0,esk4_0))=k3_xboole_0(esk5_0,esk4_0)|r2_hidden(esk7_0,k3_xboole_0(esk5_0,esk4_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 1.82/2.03  cnf(c_0_65, negated_conjecture, (r2_hidden(esk2_2(esk5_0,X1),esk5_0)|~r2_hidden(X2,k3_xboole_0(esk5_0,k3_tarski(k2_enumset1(X1,X1,X1,esk6_0))))), inference(spm,[status(thm)],[c_0_30, c_0_57])).
% 1.82/2.03  cnf(c_0_66, negated_conjecture, (r2_hidden(esk3_2(esk5_0,k3_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0))),k3_xboole_0(esk5_0,k3_tarski(k2_enumset1(esk4_0,esk4_0,esk4_0,esk6_0))))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 1.82/2.03  cnf(c_0_67, negated_conjecture, (r1_xboole_0(esk5_0,k3_tarski(k2_enumset1(X1,X1,X1,esk6_0)))|r2_hidden(esk2_2(esk5_0,X1),X1)), inference(spm,[status(thm)],[c_0_50, c_0_60])).
% 1.82/2.03  cnf(c_0_68, negated_conjecture, (k3_xboole_0(X1,k3_xboole_0(esk6_0,esk5_0))=k3_xboole_0(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_61, c_0_56])).
% 1.82/2.03  cnf(c_0_69, negated_conjecture, (~r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_62, c_0_38])).
% 1.82/2.03  cnf(c_0_70, negated_conjecture, (k3_xboole_0(X1,k3_xboole_0(esk5_0,esk4_0))=k3_xboole_0(esk5_0,esk4_0)|r2_hidden(esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 1.82/2.03  cnf(c_0_71, negated_conjecture, (r2_hidden(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.82/2.03  cnf(c_0_72, plain, (r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2))|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_62, c_0_52])).
% 1.82/2.03  cnf(c_0_73, negated_conjecture, (r2_hidden(esk2_2(esk5_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 1.82/2.03  cnf(c_0_74, negated_conjecture, (r2_hidden(esk2_2(esk5_0,X1),X1)|~r2_hidden(X2,k3_xboole_0(esk5_0,k3_tarski(k2_enumset1(X1,X1,X1,esk6_0))))), inference(spm,[status(thm)],[c_0_30, c_0_67])).
% 1.82/2.03  cnf(c_0_75, negated_conjecture, (k3_xboole_0(k3_xboole_0(esk6_0,esk5_0),X1)=k3_xboole_0(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_34, c_0_68])).
% 1.82/2.03  cnf(c_0_76, negated_conjecture, (k3_xboole_0(X1,k3_xboole_0(esk5_0,esk4_0))=k3_xboole_0(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])])).
% 1.82/2.03  cnf(c_0_77, negated_conjecture, (r2_hidden(esk3_2(X1,esk5_0),k3_xboole_0(X1,esk5_0))|~r2_hidden(esk2_2(esk5_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 1.82/2.03  cnf(c_0_78, negated_conjecture, (r2_hidden(esk2_2(esk5_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_74, c_0_66])).
% 1.82/2.03  cnf(c_0_79, negated_conjecture, (k3_xboole_0(esk5_0,esk4_0)=k3_xboole_0(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 1.82/2.03  cnf(c_0_80, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_34]), c_0_79]), c_0_61]), ['proof']).
% 1.82/2.03  # SZS output end CNFRefutation
% 1.82/2.03  # Proof object total steps             : 81
% 1.82/2.03  # Proof object clause steps            : 54
% 1.82/2.03  # Proof object formula steps           : 27
% 1.82/2.03  # Proof object conjectures             : 32
% 1.82/2.03  # Proof object clause conjectures      : 29
% 1.82/2.03  # Proof object formula conjectures     : 3
% 1.82/2.03  # Proof object initial clauses used    : 20
% 1.82/2.03  # Proof object initial formulas used   : 13
% 1.82/2.03  # Proof object generating inferences   : 27
% 1.82/2.03  # Proof object simplifying inferences  : 19
% 1.82/2.03  # Training examples: 0 positive, 0 negative
% 1.82/2.03  # Parsed axioms                        : 13
% 1.82/2.03  # Removed by relevancy pruning/SinE    : 0
% 1.82/2.03  # Initial clauses                      : 26
% 1.82/2.03  # Removed in clause preprocessing      : 4
% 1.82/2.03  # Initial clauses in saturation        : 22
% 1.82/2.03  # Processed clauses                    : 7875
% 1.82/2.03  # ...of these trivial                  : 656
% 1.82/2.03  # ...subsumed                          : 4032
% 1.82/2.03  # ...remaining for further processing  : 3187
% 1.82/2.03  # Other redundant clauses eliminated   : 3
% 1.82/2.03  # Clauses deleted for lack of memory   : 0
% 1.82/2.03  # Backward-subsumed                    : 3
% 1.82/2.03  # Backward-rewritten                   : 17
% 1.82/2.03  # Generated clauses                    : 274543
% 1.82/2.03  # ...of the previous two non-trivial   : 224097
% 1.82/2.03  # Contextual simplify-reflections      : 0
% 1.82/2.03  # Paramodulations                      : 274520
% 1.82/2.03  # Factorizations                       : 20
% 1.82/2.03  # Equation resolutions                 : 3
% 1.82/2.03  # Propositional unsat checks           : 0
% 1.82/2.03  #    Propositional check models        : 0
% 1.82/2.03  #    Propositional check unsatisfiable : 0
% 1.82/2.03  #    Propositional clauses             : 0
% 1.82/2.03  #    Propositional clauses after purity: 0
% 1.82/2.03  #    Propositional unsat core size     : 0
% 1.82/2.03  #    Propositional preprocessing time  : 0.000
% 1.82/2.03  #    Propositional encoding time       : 0.000
% 1.82/2.03  #    Propositional solver time         : 0.000
% 1.82/2.03  #    Success case prop preproc time    : 0.000
% 1.82/2.03  #    Success case prop encoding time   : 0.000
% 1.82/2.03  #    Success case prop solver time     : 0.000
% 1.82/2.03  # Current number of processed clauses  : 3142
% 1.82/2.03  #    Positive orientable unit clauses  : 1039
% 1.82/2.03  #    Positive unorientable unit clauses: 1
% 1.82/2.03  #    Negative unit clauses             : 371
% 1.82/2.03  #    Non-unit-clauses                  : 1731
% 1.82/2.03  # Current number of unprocessed clauses: 216124
% 1.82/2.03  # ...number of literals in the above   : 388040
% 1.82/2.03  # Current number of archived formulas  : 0
% 1.82/2.03  # Current number of archived clauses   : 46
% 1.82/2.03  # Clause-clause subsumption calls (NU) : 226847
% 1.82/2.03  # Rec. Clause-clause subsumption calls : 211295
% 1.82/2.03  # Non-unit clause-clause subsumptions  : 2368
% 1.82/2.03  # Unit Clause-clause subsumption calls : 23864
% 1.82/2.03  # Rewrite failures with RHS unbound    : 0
% 1.82/2.03  # BW rewrite match attempts            : 45052
% 1.82/2.03  # BW rewrite match successes           : 19
% 1.82/2.03  # Condensation attempts                : 0
% 1.82/2.03  # Condensation successes               : 0
% 1.82/2.03  # Termbank termtop insertions          : 8301322
% 1.82/2.04  
% 1.82/2.04  # -------------------------------------------------
% 1.82/2.04  # User time                : 1.614 s
% 1.82/2.04  # System time              : 0.081 s
% 1.82/2.04  # Total time               : 1.695 s
% 1.82/2.04  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
